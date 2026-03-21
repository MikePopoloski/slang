//------------------------------------------------------------------------------
// ExprEmitter.cpp
// Emission of SystemVerilog expressions to LLVM IR.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "CodegenImpl.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Intrinsics.h>

#include "slang/ast/ASTVisitor.h"
#include "slang/numeric/SVInt.h"

namespace slang::codegen {

// Apply a binary bitwise op to 4-state values, propagating unknowns.
// For AND: a known-zero input forces the output to 0 (even if other is X).
// For OR:  a known-one input forces the output to 1 (even if other is X).
// For XOR: any unknown in either operand makes the result unknown.
static llvm::Value* fourStateBitwise(llvm::IRBuilder<>& B, BinaryOperator op, llvm::Value* lhs,
                                     llvm::Value* rhs, llvm::Type* resTy) {
    // lhs/rhs are i(2N); extract val (low N bits) and unk (high N bits).
    auto halfN = [](llvm::Value* v) -> unsigned {
        return llvm::cast<llvm::IntegerType>(v->getType())->getBitWidth() / 2;
    };
    auto iHalf = [&](llvm::Value* v) -> llvm::IntegerType* {
        return llvm::IntegerType::get(B.getContext(), halfN(v));
    };
    auto getV = [&](llvm::Value* v) -> llvm::Value* { return B.CreateTrunc(v, iHalf(v)); };
    auto getU = [&](llvm::Value* v) -> llvm::Value* {
        return B.CreateTrunc(B.CreateLShr(v, halfN(v)), iHalf(v));
    };
    // Re-pack iN val+unk pair back into i(2N).
    auto pack = [&](llvm::Value* val, llvm::Value* unk) -> llvm::Value* {
        unsigned N = llvm::cast<llvm::IntegerType>(val->getType())->getBitWidth();
        return B.CreateOr(B.CreateZExt(val, resTy), B.CreateShl(B.CreateZExt(unk, resTy), N));
    };

    llvm::Value* vl = getV(lhs);
    llvm::Value* ul = getU(lhs);
    llvm::Value* vr = getV(rhs);
    llvm::Value* ur = getU(rhs);

    llvm::Value* outVal = nullptr;
    llvm::Value* outUnk = nullptr;

    switch (op) {
        case BinaryOperator::BinaryAnd: {
            // Known-zero: bit is 0 in val and 0 in unk
            llvm::Value* knownZeroL = B.CreateAnd(B.CreateNot(vl), B.CreateNot(ul));
            llvm::Value* knownZeroR = B.CreateAnd(B.CreateNot(vr), B.CreateNot(ur));
            outUnk = B.CreateAnd(B.CreateOr(ul, ur),
                                 B.CreateNot(B.CreateOr(knownZeroL, knownZeroR)));
            outVal = B.CreateAnd(B.CreateAnd(vl, vr), B.CreateNot(outUnk));
            break;
        }
        case BinaryOperator::BinaryOr: {
            // Known-one: bit is 1 in val and 0 in unk
            llvm::Value* knownOneL = B.CreateAnd(vl, B.CreateNot(ul));
            llvm::Value* knownOneR = B.CreateAnd(vr, B.CreateNot(ur));
            outUnk = B.CreateAnd(B.CreateOr(ul, ur), B.CreateNot(B.CreateOr(knownOneL, knownOneR)));
            outVal = B.CreateAnd(B.CreateOr(vl, vr), B.CreateNot(outUnk));
            break;
        }
        default:
            // XOR, XNOR: any unknown propagates.
            outUnk = B.CreateOr(ul, ur);
            if (op == BinaryOperator::BinaryXor) {
                outVal = B.CreateAnd(B.CreateXor(vl, vr), B.CreateNot(outUnk));
            }
            else { // BinaryXnor
                outVal = B.CreateAnd(B.CreateNot(B.CreateXor(vl, vr)), B.CreateNot(outUnk));
            }
            break;
    }

    return pack(outVal, outUnk);
}

// Apply a binary arithmetic op to 4-state values.
// For arithmetic ops (+,-,*,/,%): if either operand has any unknown bit the whole result is
// all-X. Division or modulo by zero also yields all-X. For shifts: only an unknown shift
// amount makes the whole result all-X; unknown bits in the value propagate positionally.
static llvm::Value* fourStateArith(llvm::IRBuilder<>& B, BinaryOperator op, llvm::Value* lhs,
                                   llvm::Value* rhs, llvm::Type* resTy, bool isSigned) {
    // lhs/rhs are i(2N); extract val (low N bits) and unk (high N bits).
    unsigned N = llvm::cast<llvm::IntegerType>(resTy)->getBitWidth() / 2;
    auto iN = llvm::IntegerType::get(B.getContext(), N);
    auto getV = [&](llvm::Value* v) -> llvm::Value* { return B.CreateTrunc(v, iN); };
    auto getU = [&](llvm::Value* v) -> llvm::Value* {
        return B.CreateTrunc(B.CreateLShr(v, N), iN);
    };
    auto pack = [&](llvm::Value* val, llvm::Value* unk) -> llvm::Value* {
        return B.CreateOr(B.CreateZExt(val, resTy), B.CreateShl(B.CreateZExt(unk, resTy), N));
    };

    llvm::Value* vl = getV(lhs);
    llvm::Value* ul = getU(lhs);
    llvm::Value* vr = getV(rhs);
    llvm::Value* ur = getU(rhs);

    auto zero = llvm::ConstantInt::get(iN, 0);
    auto allOnes = llvm::ConstantInt::getAllOnesValue(iN);

    // Shifts: only an unknown shift amount makes the result all-X. Unknown bits in the value
    // being shifted propagate positionally through the shift (same as SVInt::shl/lshr/ashr).
    bool isShift =
        (op == BinaryOperator::LogicalShiftLeft || op == BinaryOperator::LogicalShiftRight ||
         op == BinaryOperator::ArithmeticShiftLeft || op == BinaryOperator::ArithmeticShiftRight);
    if (isShift) {
        llvm::Value* hasUnkR = B.CreateICmpNE(ur, zero);
        llvm::Value* shiftedVal = nullptr;
        llvm::Value* shiftedUnk = nullptr;
        switch (op) {
            case BinaryOperator::LogicalShiftLeft:
            case BinaryOperator::ArithmeticShiftLeft:
                shiftedVal = B.CreateShl(vl, vr);
                shiftedUnk = B.CreateShl(ul, vr);
                break;
            case BinaryOperator::LogicalShiftRight:
                shiftedVal = B.CreateLShr(vl, vr);
                shiftedUnk = B.CreateLShr(ul, vr);
                break;
            default: // ArithmeticShiftRight
                // Use AShr for both val and unk so the sign-bit unknown state is propagated
                // into the vacated high bits (matching SVInt::ashr behaviour).
                shiftedVal = isSigned ? B.CreateAShr(vl, vr) : B.CreateLShr(vl, vr);
                shiftedUnk = isSigned ? B.CreateAShr(ul, vr) : B.CreateLShr(ul, vr);
                break;
        }
        llvm::Value* outVal = B.CreateSelect(hasUnkR, zero, shiftedVal);
        llvm::Value* outUnk = B.CreateSelect(hasUnkR, allOnes, shiftedUnk);
        return pack(outVal, outUnk);
    }

    // Check if either operand has any unknown bit.
    llvm::Value* hasUnkL = B.CreateICmpNE(ul, zero);
    llvm::Value* hasUnkR = B.CreateICmpNE(ur, zero);
    llvm::Value* hasUnk = B.CreateOr(hasUnkL, hasUnkR);

    // Compute the 2-state result.
    llvm::Value* computed = nullptr;
    switch (op) {
        case BinaryOperator::Add:
            computed = B.CreateAdd(vl, vr);
            break;
        case BinaryOperator::Subtract:
            computed = B.CreateSub(vl, vr);
            break;
        case BinaryOperator::Multiply:
            computed = B.CreateMul(vl, vr);
            break;
        case BinaryOperator::Divide: {
            // Division by zero also produces all-X; guard against LLVM UB with a safe divisor.
            auto one = llvm::ConstantInt::get(iN, 1);
            auto isZero = B.CreateICmpEQ(vr, zero);
            auto safeDivisor = B.CreateSelect(isZero, one, vr);
            computed = isSigned ? B.CreateSDiv(vl, safeDivisor) : B.CreateUDiv(vl, safeDivisor);
            hasUnk = B.CreateOr(hasUnk, isZero);
            break;
        }
        case BinaryOperator::Mod: {
            // Mod by zero also produces all-X; guard against LLVM UB with a safe divisor.
            auto one = llvm::ConstantInt::get(iN, 1);
            auto isZero = B.CreateICmpEQ(vr, zero);
            auto safeDivisor = B.CreateSelect(isZero, one, vr);
            computed = isSigned ? B.CreateSRem(vl, safeDivisor) : B.CreateURem(vl, safeDivisor);
            hasUnk = B.CreateOr(hasUnk, isZero);
            break;
        }
        default:
            computed = zero;
            break;
    }

    // If any unknown: result val = 0, unk = all-ones; else val = computed, unk = 0.
    llvm::Value* outVal = B.CreateSelect(hasUnk, zero, computed);
    llvm::Value* outUnk = B.CreateSelect(hasUnk, allOnes, zero);
    return pack(outVal, outUnk);
}

// Emit an arithmetic/bitwise op on two 2-state integer values.
static llvm::Value* twoStateArith(llvm::IRBuilder<>& B, BinaryOperator op, llvm::Value* lhs,
                                  llvm::Value* rhs, bool isSigned) {
    switch (op) {
        case BinaryOperator::Add:
            return B.CreateAdd(lhs, rhs);
        case BinaryOperator::Subtract:
            return B.CreateSub(lhs, rhs);
        case BinaryOperator::Multiply:
            return B.CreateMul(lhs, rhs);
        case BinaryOperator::Divide:
            return isSigned ? B.CreateSDiv(lhs, rhs) : B.CreateUDiv(lhs, rhs);
        case BinaryOperator::Mod:
            return isSigned ? B.CreateSRem(lhs, rhs) : B.CreateURem(lhs, rhs);
        case BinaryOperator::BinaryAnd:
            return B.CreateAnd(lhs, rhs);
        case BinaryOperator::BinaryOr:
            return B.CreateOr(lhs, rhs);
        case BinaryOperator::BinaryXor:
            return B.CreateXor(lhs, rhs);
        case BinaryOperator::BinaryXnor:
            return B.CreateNot(B.CreateXor(lhs, rhs));
        case BinaryOperator::LogicalShiftLeft:
            return B.CreateShl(lhs, rhs);
        case BinaryOperator::LogicalShiftRight:
            return B.CreateLShr(lhs, rhs);
        case BinaryOperator::ArithmeticShiftLeft:
            return B.CreateShl(lhs, rhs);
        case BinaryOperator::ArithmeticShiftRight:
            return isSigned ? B.CreateAShr(lhs, rhs) : B.CreateLShr(lhs, rhs);
        default:
            return lhs; // unreachable in practice
    }
}

/// Emit a comparison on two 2-state integer values, returning i1.
static llvm::Value* twoStateICmp(llvm::IRBuilder<>& B, BinaryOperator op, llvm::Value* lhs,
                                 llvm::Value* rhs, bool isSigned) {
    switch (op) {
        case BinaryOperator::Equality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::WildcardEquality:
            return B.CreateICmpEQ(lhs, rhs);
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::WildcardInequality:
            return B.CreateICmpNE(lhs, rhs);
        case BinaryOperator::GreaterThan:
            return isSigned ? B.CreateICmpSGT(lhs, rhs) : B.CreateICmpUGT(lhs, rhs);
        case BinaryOperator::GreaterThanEqual:
            return isSigned ? B.CreateICmpSGE(lhs, rhs) : B.CreateICmpUGE(lhs, rhs);
        case BinaryOperator::LessThan:
            return isSigned ? B.CreateICmpSLT(lhs, rhs) : B.CreateICmpULT(lhs, rhs);
        case BinaryOperator::LessThanEqual:
            return isSigned ? B.CreateICmpSLE(lhs, rhs) : B.CreateICmpULE(lhs, rhs);
        default:
            return B.CreateICmpEQ(lhs, rhs);
    }
}

static llvm::Value* emitBitwiseReduction(IRBuilder& B, UnaryOperator op, llvm::Value* operand,
                                         llvm::Type* resultType, bool fourState) {
    if (fourState) {
        auto [val, unk] = B.getIntParts(operand);
        auto iN = val->getType();
        auto zero = llvm::ConstantInt::get(iN, 0);
        auto hasUnk = B.CreateICmpNE(unk, zero);

        bool negate = false;
        switch (op) {
            case UnaryOperator::BitwiseAnd:
            case UnaryOperator::BitwiseNand: {
                // "no definite zero" iff every bit position is either 1 or unknown: (val | unk)
                auto allOnes = llvm::ConstantInt::getAllOnesValue(iN);
                auto noDefZero = B.CreateICmpEQ(B.CreateOr(val, unk), allOnes);
                val = B.CreateAnd(noDefZero, B.CreateNot(hasUnk));
                unk = B.CreateAnd(noDefZero, hasUnk);
                negate = op == UnaryOperator::BitwiseNand;
                break;
            }
            case UnaryOperator::BitwiseOr:
            case UnaryOperator::BitwiseNor: {
                // definite ones: bits that are set in val but not flagged as unknown
                auto defOnes = B.CreateAnd(val, B.CreateNot(unk));
                auto hasDefOne = B.CreateICmpNE(defOnes, zero);
                val = hasDefOne;
                unk = B.CreateAnd(B.CreateNot(hasDefOne), hasUnk);
                negate = op == UnaryOperator::BitwiseNor;
                break;
            }
            case UnaryOperator::BitwiseXor:
            case UnaryOperator::BitwiseXnor: {
                auto one = llvm::ConstantInt::get(iN, 1);
                auto popcount = B.CreateUnaryIntrinsic(llvm::Intrinsic::ctpop, val);
                auto parity = B.CreateICmpNE(B.CreateAnd(popcount, one), zero);
                // val bit is the parity only when no unknowns; masked to 0 when result is X
                val = B.CreateAnd(parity, B.CreateNot(hasUnk));
                unk = hasUnk;
                negate = op == UnaryOperator::BitwiseXnor;
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }

        if (negate) {
            // new_val = ~val & ~unk;  new_unk = unk (unchanged).
            val = B.CreateAnd(B.CreateNot(val), B.CreateNot(unk));
        }
        return B.createSVInt(val, unk, resultType);
    }
    else {
        switch (op) {
            case UnaryOperator::BitwiseAnd:
            case UnaryOperator::BitwiseNand: {
                auto allOnes = llvm::ConstantInt::getAllOnesValue(operand->getType());
                return op == UnaryOperator::BitwiseAnd ? B.CreateICmpEQ(operand, allOnes)
                                                       : B.CreateICmpNE(operand, allOnes);
            }
            case UnaryOperator::BitwiseOr:
            case UnaryOperator::BitwiseNor: {
                auto zero = llvm::ConstantInt::get(operand->getType(), 0);
                return op == UnaryOperator::BitwiseOr ? B.CreateICmpNE(operand, zero)
                                                      : B.CreateICmpEQ(operand, zero);
            }
            case UnaryOperator::BitwiseXor:
            case UnaryOperator::BitwiseXnor: {
                auto vTy = operand->getType();
                auto popcount = B.CreateUnaryIntrinsic(llvm::Intrinsic::ctpop, operand);
                auto parity = B.CreateAnd(popcount, llvm::ConstantInt::get(vTy, 1));
                auto i1 = B.CreateICmpNE(parity, llvm::ConstantInt::get(vTy, 0));
                return op == UnaryOperator::BitwiseXnor ? B.CreateNot(i1) : i1;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }
}

namespace {

struct LValueVisitor {
    FunctionEmitter& fe;

    llvm::Value* visit(const NamedValueExpression& e) {
        if (auto it = fe.locals.find(&e.symbol); it != fe.locals.end())
            return it->second;
        SLANG_UNIMPLEMENTED;
    }

    llvm::Value* visit(const HierarchicalValueExpression& e) {
        if (auto it = fe.locals.find(&e.symbol); it != fe.locals.end())
            return it->second;
        SLANG_UNIMPLEMENTED;
    }

    llvm::Value* visit(const ElementSelectExpression& e) {
        auto base = fe.emitLValue(e.value());
        if (!e.value().type->isFixedSize() || e.value().type->isIntegral())
            SLANG_UNIMPLEMENTED;
        auto idxVal = fe.emitExpr(e.selector());
        auto zero = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*fe.context.ctx), 0);
        return fe.builder.CreateGEP(fe.context.types.lower(*e.value().type), base, {zero, idxVal});
    }

    template<typename T>
    llvm::Value* visit(const T&) {
        SLANG_UNIMPLEMENTED;
    }
};

struct ExprEmitter {
    FunctionEmitter& fe;
    IRBuilder& builder;

    explicit ExprEmitter(FunctionEmitter& fe) : fe(fe), builder(fe.builder) {}

    llvm::Value* visitExpr(const Expression& e) { return e.visit(*this); }

    llvm::Value* visit(const InvalidExpression& e);
    llvm::Value* visit(const IntegerLiteral& e);
    llvm::Value* visit(const RealLiteral& e);
    llvm::Value* visit(const TimeLiteral& e);
    llvm::Value* visit(const UnbasedUnsizedIntegerLiteral& e);
    llvm::Value* visit(const NullLiteral& e);
    llvm::Value* visit(const StringLiteral& e);
    llvm::Value* visit(const NamedValueExpression& e);
    llvm::Value* visit(const HierarchicalValueExpression& e);
    llvm::Value* visit(const UnaryExpression& e);
    llvm::Value* visit(const BinaryExpression& e);
    llvm::Value* visit(const ConditionalExpression& e);
    llvm::Value* visit(const InsideExpression& e);
    llvm::Value* visit(const AssignmentExpression& e);
    llvm::Value* visit(const ConversionExpression& e);
    llvm::Value* visit(const ConcatenationExpression& e);
    llvm::Value* visit(const ReplicationExpression& e);
    llvm::Value* visit(const ElementSelectExpression& e);
    llvm::Value* visit(const RangeSelectExpression& e);
    llvm::Value* visit(const MemberAccessExpression& e);
    llvm::Value* visit(const CallExpression& e);
    llvm::Value* visit(const MinTypMaxExpression& e);
    llvm::Value* visit(const UnboundedLiteral& e);
    llvm::Value* visit(const StreamingConcatenationExpression& e);
    llvm::Value* visit(const DataTypeExpression& e);
    llvm::Value* visit(const TypeReferenceExpression& e);
    llvm::Value* visit(const ArbitrarySymbolExpression& e);
    llvm::Value* visit(const LValueReferenceExpression& e);
    llvm::Value* visit(const SimpleAssignmentPatternExpression& e);
    llvm::Value* visit(const StructuredAssignmentPatternExpression& e);
    llvm::Value* visit(const ReplicatedAssignmentPatternExpression& e);
    llvm::Value* visit(const EmptyArgumentExpression& e);
    llvm::Value* visit(const ValueRangeExpression& e);
    llvm::Value* visit(const DistExpression& e);
    llvm::Value* visit(const NewArrayExpression& e);
    llvm::Value* visit(const NewClassExpression& e);
    llvm::Value* visit(const NewCovergroupExpression& e);
    llvm::Value* visit(const CopyClassExpression& e);
    llvm::Value* visit(const ClockingEventExpression& e);
    llvm::Value* visit(const AssertionInstanceExpression& e);
    llvm::Value* visit(const TaggedUnionExpression& e);

    llvm::Value* emitConversion(llvm::Value* val, const Type& fromType, const Type& toType,
                                ConversionKind conversionKind, bool forceFloatTrunc);
};

llvm::Value* ExprEmitter::visit(const InvalidExpression& e) {
    if (e.type->isVoid())
        return nullptr;
    return llvm::PoisonValue::get(builder.types.lower(*e.type));
}

llvm::Value* ExprEmitter::visit(const IntegerLiteral& e) {
    return builder.getSVInt(e.getValue(), e.type->isFourState());
}

llvm::Value* ExprEmitter::visit(const RealLiteral& e) {
    return llvm::ConstantFP::get(builder.types.lower(*e.type), e.getValue());
}

llvm::Value* ExprEmitter::visit(const TimeLiteral& e) {
    return llvm::ConstantFP::get(builder.types.lower(*e.type), e.getValue());
}

llvm::Value* ExprEmitter::visit(const UnbasedUnsizedIntegerLiteral& e) {
    return builder.getSVInt(e.getValue(), e.type->isFourState());
}

llvm::Value* ExprEmitter::visit(const NullLiteral&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const UnboundedLiteral&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const StringLiteral&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const NamedValueExpression& e) {
    auto ptr = fe.emitLValue(e);
    auto ty = builder.types.lower(e.symbol.getType());
    return builder.CreateLoad(ty, ptr);
}

llvm::Value* ExprEmitter::visit(const HierarchicalValueExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const UnaryExpression& e) {
    auto resultType = builder.types.lower(*e.type);
    const bool fourState = e.type->isFourState();
    const bool isFloat = e.type->isFloating();

    if (OpInfo::isLValue(e.op)) {
        // Handle pre/post inc/dec operators here.
        const bool isInc = e.op == UnaryOperator::Preincrement ||
                           e.op == UnaryOperator::Postincrement;
        const bool isPre = e.op == UnaryOperator::Preincrement ||
                           e.op == UnaryOperator::Predecrement;
        const int amount = (isInc ? 1 : -1);

        auto ptr = fe.emitLValue(e.operand());
        auto opTy = builder.types.lower(*e.operand().type);
        auto oldVal = builder.CreateLoad(opTy, ptr);

        llvm::Value* newVal;
        if (isFloat) {
            auto one = oldVal->getType()->isFloatTy()
                           ? llvm::ConstantFP::get(opTy, static_cast<float>(amount))
                           : llvm::ConstantFP::get(opTy, static_cast<double>(amount));
            newVal = builder.CreateFAdd(oldVal, one, isInc ? "inc" : "dec");
        }
        else if (!fourState) {
            auto one = llvm::ConstantInt::getSigned(opTy, amount);
            newVal = builder.CreateAdd(oldVal, one, isInc ? "inc" : "dec");
        }
        else {
            auto [vl, ul] = builder.getIntParts(oldVal);
            auto iN = vl->getType();
            auto one = llvm::ConstantInt::getSigned(iN, amount);
            auto nv = builder.CreateAdd(vl, one, isInc ? "inc" : "dec");

            auto zero = llvm::ConstantInt::get(iN, 0);
            auto hasUnk = builder.CreateICmpNE(ul, zero);

            // The final result is all X's if any unknowns.
            auto outVal = builder.CreateSelect(hasUnk, zero, nv);
            auto outUnk = builder.CreateSelect(hasUnk, llvm::ConstantInt::getAllOnesValue(iN),
                                               zero);
            newVal = builder.createSVInt(outVal, outUnk, opTy);
        }

        builder.CreateStore(newVal, ptr);
        return isPre ? newVal : oldVal;
    }

    auto operand = visitExpr(e.operand());
    switch (e.op) {
        case UnaryOperator::Plus:
            // Plus does nothing. Note: some simulators will convert four state operands
            // that contain any unknown bits into all Xs, while others leave them alone.
            // We might want a flag for that behavior at some point.
            return operand;
        case UnaryOperator::Minus:
            if (isFloat)
                return builder.CreateFNeg(operand);

            if (fourState) {
                auto [vl, ul] = builder.getIntParts(operand);
                auto iN = vl->getType();
                auto zero = llvm::ConstantInt::get(iN, 0);
                auto allOnes = llvm::ConstantInt::getAllOnesValue(iN);
                auto hasUnk = builder.CreateICmpNE(ul, zero);
                auto outVal = builder.CreateSelect(hasUnk, zero, builder.CreateNeg(vl));
                auto outUnk = builder.CreateSelect(hasUnk, allOnes, zero);
                return builder.createSVInt(outVal, outUnk, resultType);
            }
            return builder.CreateNeg(operand);
        case UnaryOperator::BitwiseNot:
            if (fourState) {
                // Any unknown bits are still unknown, but we need to make sure
                // any high impedance values become X's
                auto [vl, ul] = builder.getIntParts(operand);
                auto nv = builder.CreateAnd(builder.CreateNot(vl), builder.CreateNot(ul));
                return builder.createSVInt(nv, ul, resultType);
            }
            return builder.CreateNot(operand);
        case UnaryOperator::LogicalNot: {
            // Result is always a single bit (four-state when operand is four-state).
            if (fourState) {
                SLANG_ASSERT(e.operand().type->isFourState());
                auto [val, unk] = builder.getIntParts(operand);
                auto zero = llvm::ConstantInt::get(val->getType(), 0);
                // !X=X, !nonzero=0, !zero=1 => val = (val==0) & (unk==0), unk = (unk!=0)
                auto hasUnk = builder.CreateICmpNE(unk, zero);
                auto isZero = builder.CreateICmpEQ(val, zero);
                auto i1_val = builder.CreateAnd(isZero, builder.CreateNot(hasUnk));
                return builder.createSVInt(i1_val, hasUnk, resultType);
            }

            // Non-four-state: use emitCond to handle any boolean-convertible operand type.
            auto cond = fe.emitCond(e.operand());
            auto notCond = builder.CreateNot(cond);
            return resultType->isIntegerTy(1) ? notCond : builder.CreateZExt(notCond, resultType);
        }
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseXnor:
            return emitBitwiseReduction(builder, e.op, operand, resultType, fourState);
        default:
            SLANG_UNREACHABLE;
    }
}

llvm::Value* ExprEmitter::visit(const BinaryExpression& e) {
    auto ty = builder.types.lower(*e.type);
    const BinaryOperator op = e.op;
    const bool isSigned = e.left().type->isSigned();
    const bool lhs4 = e.left().type->isFourState();
    const bool rhs4 = e.right().type->isFourState();
    const bool fourState = lhs4 || rhs4;
    // Check operand type too: comparisons of float values have integer result type
    const bool isFloat = e.type->isFloating() || e.left().type->isFloating();

    if (op == BinaryOperator::LogicalAnd || op == BinaryOperator::LogicalOr) {
        auto condL = fe.emitCond(e.left());
        auto rhsBB = llvm::BasicBlock::Create(*fe.context.ctx, "logic.rhs", fe.currentFunc);
        auto mergeBB = llvm::BasicBlock::Create(*fe.context.ctx, "logic.merge", fe.currentFunc);

        if (op == BinaryOperator::LogicalAnd)
            builder.CreateCondBr(condL, rhsBB, mergeBB);
        else
            builder.CreateCondBr(condL, mergeBB, rhsBB);

        auto lhsBB = builder.GetInsertBlock();

        builder.SetInsertPoint(rhsBB);
        auto condR = fe.emitCond(e.right());
        auto rhsEndBB = builder.GetInsertBlock();
        builder.CreateBr(mergeBB);

        builder.SetInsertPoint(mergeBB);
        auto phi = builder.CreatePHI(llvm::Type::getInt1Ty(*fe.context.ctx), 2);
        if (op == BinaryOperator::LogicalAnd) {
            phi->addIncoming(llvm::ConstantInt::getFalse(*fe.context.ctx), lhsBB);
            phi->addIncoming(condR, rhsEndBB);
        }
        else {
            phi->addIncoming(llvm::ConstantInt::getTrue(*fe.context.ctx), lhsBB);
            phi->addIncoming(condR, rhsEndBB);
        }

        if (ty->isIntegerTy(1))
            return phi;
        if (e.type->isFourState())
            return builder.toFourState(phi, ty);
        return builder.CreateZExt(phi, ty);
    }

    if (op == BinaryOperator::LogicalImplication || op == BinaryOperator::LogicalEquivalence) {
        auto l = fe.emitCond(e.left());
        auto r = fe.emitCond(e.right());
        llvm::Value* result = nullptr;
        if (op == BinaryOperator::LogicalImplication)
            result = builder.CreateOr(builder.CreateNot(l), r);
        else
            result = builder.CreateICmpEQ(l, r);
        if (ty->isIntegerTy(1))
            return result;
        if (e.type->isFourState())
            return builder.toFourState(result, ty);
        return builder.CreateZExt(result, ty);
    }

    if (isFloat) {
        auto lhs = fe.emitExpr(e.left());
        auto rhs = fe.emitExpr(e.right());
        switch (op) {
            case BinaryOperator::Add:
                return builder.CreateFAdd(lhs, rhs);
            case BinaryOperator::Subtract:
                return builder.CreateFSub(lhs, rhs);
            case BinaryOperator::Multiply:
                return builder.CreateFMul(lhs, rhs);
            case BinaryOperator::Divide:
                return builder.CreateFDiv(lhs, rhs);
            case BinaryOperator::Mod:
                return builder.CreateFRem(lhs, rhs);
            case BinaryOperator::Power: {
                auto powFn = llvm::Intrinsic::getOrInsertDeclaration(fe.context.module.get(),
                                                                     llvm::Intrinsic::pow,
                                                                     {lhs->getType()});
                return builder.CreateCall(powFn, {lhs, rhs});
            }
            case BinaryOperator::Equality:
                return builder.CreateZExt(builder.CreateFCmpOEQ(lhs, rhs), ty);
            case BinaryOperator::Inequality:
                return builder.CreateZExt(builder.CreateFCmpONE(lhs, rhs), ty);
            case BinaryOperator::GreaterThan:
                return builder.CreateZExt(builder.CreateFCmpOGT(lhs, rhs), ty);
            case BinaryOperator::GreaterThanEqual:
                return builder.CreateZExt(builder.CreateFCmpOGE(lhs, rhs), ty);
            case BinaryOperator::LessThan:
                return builder.CreateZExt(builder.CreateFCmpOLT(lhs, rhs), ty);
            case BinaryOperator::LessThanEqual:
                return builder.CreateZExt(builder.CreateFCmpOLE(lhs, rhs), ty);
            default:
                return llvm::Constant::getNullValue(ty);
        }
    }

    auto lhs = fe.emitExpr(e.left());
    auto rhs = fe.emitExpr(e.right());

    bool isComparison = op >= BinaryOperator::Equality && op <= BinaryOperator::WildcardInequality;

    if (fourState) {
        auto opStructTy = builder.types.lower(*e.left().type);
        if (!lhs4 && llvm::isa<llvm::IntegerType>(lhs->getType()))
            lhs = builder.toFourState(lhs, opStructTy);
        if (!rhs4 && llvm::isa<llvm::IntegerType>(rhs->getType()))
            rhs = builder.toFourState(rhs, opStructTy);

        bool isBitwise = op == BinaryOperator::BinaryAnd || op == BinaryOperator::BinaryOr ||
                         op == BinaryOperator::BinaryXor || op == BinaryOperator::BinaryXnor;

        if (isBitwise)
            return fourStateBitwise(builder, op, lhs, rhs, ty);

        if (isComparison) {
            auto vl = builder.getValPart(lhs);
            auto ul = builder.getUnkPart(lhs);
            auto vr = builder.getValPart(rhs);
            auto ur = builder.getUnkPart(rhs);
            auto iN = vl->getType();
            auto zero = llvm::ConstantInt::get(iN, 0);
            llvm::Value* hasUnk = builder.CreateOr(builder.CreateICmpNE(ul, zero),
                                                   builder.CreateICmpNE(ur, zero));
            auto cmpResult = twoStateICmp(builder, op, vl, vr, isSigned);
            auto i1False = llvm::ConstantInt::getFalse(*fe.context.ctx);
            auto outVal = builder.CreateSelect(hasUnk, i1False, cmpResult);
            auto outUnk = hasUnk;
            if (e.type->isFourState())
                return builder.createSVInt(outVal, outUnk, ty);
            return ty->isIntegerTy(1) ? outVal : builder.CreateZExt(outVal, ty);
        }

        return fourStateArith(builder, op, lhs, rhs, ty, isSigned);
    }

    if (isComparison) {
        auto i1 = twoStateICmp(builder, op, lhs, rhs, isSigned);
        if (ty->isIntegerTy(1))
            return i1;
        return builder.CreateZExt(i1, ty);
    }

    if (op == BinaryOperator::Power) {
        auto doubleTy = llvm::Type::getDoubleTy(*fe.context.ctx);
        auto lhsF = isSigned ? builder.CreateSIToFP(lhs, doubleTy)
                             : builder.CreateUIToFP(lhs, doubleTy);
        auto rhsF = isSigned ? builder.CreateSIToFP(rhs, doubleTy)
                             : builder.CreateUIToFP(rhs, doubleTy);
        auto powFn = llvm::Intrinsic::getOrInsertDeclaration(fe.context.module.get(),
                                                             llvm::Intrinsic::pow, {doubleTy});
        auto resultF = builder.CreateCall(powFn, {lhsF, rhsF});
        return isSigned ? builder.CreateFPToSI(resultF, ty) : builder.CreateFPToUI(resultF, ty);
    }

    return twoStateArith(builder, op, lhs, rhs, isSigned);
}

llvm::Value* ExprEmitter::visit(const ConditionalExpression& e) {
    llvm::Value* condVal = nullptr;
    for (auto& c : e.conditions) {
        auto cv = fe.emitCond(*c.expr);
        condVal = condVal ? builder.CreateAnd(condVal, cv) : cv;
    }
    if (!condVal)
        condVal = llvm::ConstantInt::getTrue(*fe.context.ctx);
    auto lhsV = fe.emitExpr(e.left());
    auto rhsV = fe.emitExpr(e.right());
    return builder.CreateSelect(condVal, lhsV, rhsV);
}

llvm::Value* ExprEmitter::visit(const InsideExpression& e) {
    auto ty = builder.types.lower(*e.type);
    auto lhs = fe.emitExpr(e.left());

    llvm::Value* result = llvm::ConstantInt::getFalse(*fe.context.ctx);
    for (auto rangeExpr : e.rangeList()) {
        if (auto vr = rangeExpr->as_if<ValueRangeExpression>()) {
            // Range comparison: lo <= lhs <= hi
            auto lo = fe.emitExpr(vr->left());
            auto hi = fe.emitExpr(vr->right());
            const bool isSigned = vr->left().type->isSigned();
            llvm::Value* inRange;
            if (isSigned) {
                inRange = builder.CreateAnd(builder.CreateICmpSLE(lo, lhs),
                                            builder.CreateICmpSLE(lhs, hi));
            }
            else {
                inRange = builder.CreateAnd(builder.CreateICmpULE(lo, lhs),
                                            builder.CreateICmpULE(lhs, hi));
            }
            result = builder.CreateOr(result, inRange);
        }
        else {
            auto cmp = builder.CreateICmpEQ(lhs, fe.emitExpr(*rangeExpr));
            result = builder.CreateOr(result, cmp);
        }
    }

    if (ty->isIntegerTy(1))
        return result;
    if (e.type->isFourState())
        return builder.toFourState(result, ty);
    return builder.CreateZExt(result, ty);
}

llvm::Value* ExprEmitter::visit(const AssignmentExpression& e) {
    auto rhsV = fe.emitExpr(e.right());
    auto lhsPtr = fe.emitLValue(e.left());

    if (e.isCompound()) {
        auto lhsTy = builder.types.lower(*e.left().type);
        auto lhsV = builder.CreateLoad(lhsTy, lhsPtr);
        const bool isSigned = e.left().type->isSigned();
        if (e.left().type->isFloating()) {
            switch (*e.op) {
                case BinaryOperator::Add:
                    rhsV = builder.CreateFAdd(lhsV, rhsV);
                    break;
                case BinaryOperator::Subtract:
                    rhsV = builder.CreateFSub(lhsV, rhsV);
                    break;
                case BinaryOperator::Multiply:
                    rhsV = builder.CreateFMul(lhsV, rhsV);
                    break;
                case BinaryOperator::Divide:
                    rhsV = builder.CreateFDiv(lhsV, rhsV);
                    break;
                default:
                    break;
            }
        }
        else if (e.left().type->isFourState()) {
            auto resTy = builder.types.lower(*e.left().type);
            bool isBitwise = *e.op == BinaryOperator::BinaryAnd ||
                             *e.op == BinaryOperator::BinaryOr ||
                             *e.op == BinaryOperator::BinaryXor ||
                             *e.op == BinaryOperator::BinaryXnor;
            if (isBitwise)
                rhsV = fourStateBitwise(builder, *e.op, lhsV, rhsV, resTy);
            else
                rhsV = fourStateArith(builder, *e.op, lhsV, rhsV, resTy, isSigned);
        }
        else {
            rhsV = twoStateArith(builder, *e.op, lhsV, rhsV, isSigned);
        }
    }

    builder.CreateStore(rhsV, lhsPtr);
    return rhsV;
}

llvm::Value* ExprEmitter::visit(const ConversionExpression& e) {
    return emitConversion(fe.emitExpr(e.operand()), e.operand().type->getCanonicalType(),
                          e.type->getCanonicalType(), e.conversionKind,
                          /* forceFloatTrunc */ false);
}

llvm::Value* ExprEmitter::emitConversion(llvm::Value* val, const Type& fromType, const Type& toType,
                                         ConversionKind conversionKind, bool forceFloatTrunc) {
    if (conversionKind == ConversionKind::StreamingConcat ||
        conversionKind == ConversionKind::BitstreamCast) {
        SLANG_UNIMPLEMENTED;
    }

    if (fromType.isMatching(toType))
        return val;

    auto resultTy = builder.types.lower(toType);

    if (toType.isIntegral()) {
        if (fromType.isIntegral()) {
            const bitwidth_t fromBits = fromType.getBitWidth();
            const bitwidth_t toBits = toType.getBitWidth();
            const bool fromFourState = fromType.isFourState();
            const bool toFourState = toType.isFourState();

            // Extract the value (and unknown) parts from the source.
            llvm::Value* srcVal = nullptr;
            llvm::Value* srcUnk = nullptr;
            if (fromFourState) {
                srcVal = builder.getValPart(val);
                srcUnk = builder.getUnkPart(val);
            }
            else {
                srcVal = val;
                srcUnk = llvm::ConstantInt::get(val->getType(), 0);
            }

            // If going 4-state -> 2-state, clear unknown bits (X/Z become 0).
            if (!toFourState && fromFourState) {
                srcVal = builder.CreateAnd(srcVal, builder.CreateNot(srcUnk));
                srcUnk = llvm::ConstantInt::get(srcVal->getType(), 0);
            }

            // For Propagated conversions the LRM says to sign-extend if the
            // *target* type is signed; for all other conversion kinds, sign-extend
            // if the *source* type is signed.
            const bool signExtend = conversionKind == ConversionKind::Propagated
                                        ? toType.isSigned()
                                        : fromType.isSigned();

            auto dstHalfTy = builder.types.twoStateFor(toBits);
            llvm::Value* dstVal = nullptr;
            llvm::Value* dstUnk = nullptr;

            if (toBits == fromBits) {
                // Same width - just reinterpret (possibly changing sign, no bit change).
                dstVal = srcVal;
                dstUnk = srcUnk;
            }
            else if (toBits < fromBits) {
                // Truncate: take the low toBits of both parts.
                dstVal = builder.CreateTrunc(srcVal, dstHalfTy);
                dstUnk = builder.CreateTrunc(srcUnk, dstHalfTy);
            }
            else {
                // Extend: either sign-extend or zero-extend.
                // Unknown propagation: if the MSB of the source is unknown and we sign-extend,
                // the extended bits should all be unknown too .
                if (signExtend) {
                    dstVal = builder.CreateSExt(srcVal, dstHalfTy);
                    dstUnk = builder.CreateSExt(srcUnk, dstHalfTy);
                }
                else {
                    dstVal = builder.CreateZExt(srcVal, dstHalfTy);
                    dstUnk = builder.CreateZExt(srcUnk, dstHalfTy);
                }
            }

            return toFourState ? builder.createSVInt(dstVal, dstUnk, resultTy) : dstVal;
        }
        else if (fromType.isFloating()) {
            auto convIntr = toType.isSigned() ? llvm::Intrinsic::fptosi_sat
                                              : llvm::Intrinsic::fptoui_sat;
            auto dstHalfTy = builder.types.twoStateFor(toType.getBitWidth());

            // Use llvm.round to round to nearest (ties away from zero), unless opted
            // out via the parameter flag.
            if (!forceFloatTrunc)
                val = builder.CreateUnaryIntrinsic(llvm::Intrinsic::round, val);

            // Use saturating conversion intrinsics to avoid UB for out-of-range values.
            val = builder.CreateIntrinsic(convIntr, {dstHalfTy, val->getType()}, {val});

            return toType.isFourState() ? builder.toFourState(val) : val;
        }
    }
    else if (toType.isFloating()) {
        if (fromType.isIntegral()) {
            // Integer-to-float: unknown bits become zero bits before conversion.
            auto srcVal = val;
            if (fromType.isFourState()) {
                auto [v, u] = builder.getIntParts(val);
                srcVal = builder.CreateAnd(v, builder.CreateNot(u));
            }

            if (fromType.isSigned())
                return builder.CreateSIToFP(srcVal, resultTy);
            else
                return builder.CreateUIToFP(srcVal, resultTy);
        }
        else if (fromType.isFloating()) {
            // Simple case, just extend or trunc.
            if (resultTy->isDoubleTy())
                return builder.CreateFPExt(val, resultTy);
            else
                return builder.CreateFPTrunc(val, resultTy);
        }
    }

    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const ConcatenationExpression& e) {
    auto ty = builder.types.lower(*e.type);
    unsigned totalBits = e.type->getBitWidth();

    const bool fourState = e.type->isFourState();
    auto iTotal = builder.types.twoStateFor(totalBits);
    auto zero = llvm::ConstantInt::get(iTotal, 0);

    llvm::Value* accVal = zero;
    llvm::Value* accUnk = zero;

    unsigned shift = totalBits;
    for (auto op : e.operands()) {
        unsigned opBits = op->type->getBitWidth();
        shift -= opBits;
        auto opV = fe.emitExpr(*op);

        llvm::Value* vBits = nullptr;
        llvm::Value* uBits = nullptr;

        if (op->type->isFourState()) {
            vBits = builder.getValPart(opV);
            uBits = builder.getUnkPart(opV);
        }
        else {
            vBits = opV->getType()->isIntegerTy() ? opV : zero;
            uBits = llvm::ConstantInt::get(opBits > 0 ? builder.types.twoStateFor(opBits) : iTotal,
                                           0);
        }

        if (vBits->getType()->getIntegerBitWidth() < totalBits)
            vBits = builder.CreateZExt(vBits, iTotal);
        if (uBits->getType()->getIntegerBitWidth() < totalBits)
            uBits = builder.CreateZExt(uBits, iTotal);

        auto shiftConst = llvm::ConstantInt::get(iTotal, shift);
        accVal = builder.CreateOr(accVal, builder.CreateShl(vBits, shiftConst));
        accUnk = builder.CreateOr(accUnk, builder.CreateShl(uBits, shiftConst));
    }

    if (fourState)
        return builder.createSVInt(accVal, accUnk, ty);
    return accVal;
}

llvm::Value* ExprEmitter::visit(const ReplicationExpression& e) {
    auto ty = builder.types.lower(*e.type);
    auto countExpr = fe.emitExpr(e.count());
    auto innerExpr = fe.emitExpr(e.concat());

    auto ci = llvm::dyn_cast<llvm::ConstantInt>(countExpr);
    if (!ci)
        return llvm::Constant::getNullValue(ty);

    unsigned N = static_cast<unsigned>(ci->getZExtValue());
    unsigned innerBits = e.concat().type->getBitWidth();
    unsigned totalBits = N * innerBits;

    const bool fourState = e.type->isFourState();
    auto iTotal = builder.types.twoStateFor(totalBits);
    auto zero = llvm::ConstantInt::get(iTotal, 0);

    llvm::Value* accVal = zero;
    llvm::Value* accUnk = zero;

    llvm::Value* vIn = nullptr;
    llvm::Value* uIn = nullptr;

    if (e.concat().type->isFourState()) {
        vIn = builder.getValPart(innerExpr);
        uIn = builder.getUnkPart(innerExpr);
    }
    else {
        vIn = innerExpr;
        uIn = llvm::ConstantInt::get(builder.types.twoStateFor(innerBits), 0);
    }

    if (vIn->getType()->getIntegerBitWidth() < totalBits)
        vIn = builder.CreateZExt(vIn, iTotal);
    if (uIn->getType()->getIntegerBitWidth() < totalBits)
        uIn = builder.CreateZExt(uIn, iTotal);

    for (unsigned i = 0; i < N; ++i) {
        unsigned sh = i * innerBits;
        auto shiftConst = llvm::ConstantInt::get(iTotal, sh);
        accVal = builder.CreateOr(accVal, builder.CreateShl(vIn, shiftConst));
        accUnk = builder.CreateOr(accUnk, builder.CreateShl(uIn, shiftConst));
    }

    if (fourState)
        return builder.createSVInt(accVal, accUnk, ty);
    return accVal;
}

llvm::Value* ExprEmitter::visit(const StreamingConcatenationExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const ElementSelectExpression& e) {
    auto ty = builder.types.lower(*e.type);
    const Type& valType = *e.value().type;

    if (valType.isIntegral()) {
        auto base = fe.emitExpr(e.value());
        auto idx = fe.emitExpr(e.selector());

        const bool fourState = valType.isFourState();
        llvm::Value* vBase = fourState ? builder.getValPart(base) : base;
        llvm::Value* uBase = fourState ? builder.getUnkPart(base)
                                       : llvm::ConstantInt::get(base->getType(), 0);

        if (idx->getType()->getIntegerBitWidth() < vBase->getType()->getIntegerBitWidth())
            idx = builder.CreateZExt(idx, vBase->getType());
        else if (idx->getType()->getIntegerBitWidth() > vBase->getType()->getIntegerBitWidth())
            idx = builder.CreateTrunc(idx, vBase->getType());

        auto vBit = builder.CreateAnd(builder.CreateLShr(vBase, idx),
                                      llvm::ConstantInt::get(vBase->getType(), 1));
        auto i1V = builder.CreateICmpNE(vBit, llvm::ConstantInt::get(vBase->getType(), 0));

        if (fourState) {
            auto uBit = builder.CreateAnd(builder.CreateLShr(uBase, idx),
                                          llvm::ConstantInt::get(uBase->getType(), 1));
            auto i1U = builder.CreateICmpNE(uBit, llvm::ConstantInt::get(uBase->getType(), 0));
            return builder.createSVInt(i1V, i1U, ty);
        }

        if (ty->isIntegerTy(1))
            return i1V;
        return builder.CreateZExt(i1V, ty);
    }

    auto ptr = fe.emitLValue(e);
    return builder.CreateLoad(ty, ptr);
}

llvm::Value* ExprEmitter::visit(const RangeSelectExpression& e) {
    auto ty = builder.types.lower(*e.type);
    if (!e.value().type->isIntegral())
        return llvm::Constant::getNullValue(ty);

    auto base = fe.emitExpr(e.value());
    const bool fourState = e.value().type->isFourState();
    auto vBase = fourState ? builder.getValPart(base) : base;
    auto uBase = fourState ? builder.getUnkPart(base) : llvm::ConstantInt::get(base->getType(), 0);

    auto baseTy = vBase->getType();
    unsigned width = e.type->getBitWidth();

    // Compute the LSB of the range as a Value.
    llvm::Value* shift = nullptr;
    switch (e.getSelectionKind()) {
        case RangeSelectionKind::Simple: {
            // [hi:lo] — take min(left, right) as the shift.
            auto lv = fe.emitExpr(e.left());
            auto rv = fe.emitExpr(e.right());
            if (lv->getType() != baseTy)
                lv = builder.CreateZExt(lv, baseTy);
            if (rv->getType() != baseTy)
                rv = builder.CreateZExt(rv, baseTy);
            shift = builder.CreateSelect(builder.CreateICmpULE(lv, rv), lv, rv);
            break;
        }
        case RangeSelectionKind::IndexedUp:
            // [base+:width] — shift = left
            shift = fe.emitExpr(e.left());
            if (shift->getType() != baseTy)
                shift = builder.CreateZExt(shift, baseTy);
            break;
        case RangeSelectionKind::IndexedDown: {
            // [base-:width] — shift = left - width + 1
            auto lv = fe.emitExpr(e.left());
            if (lv->getType() != baseTy)
                lv = builder.CreateZExt(lv, baseTy);
            auto w = llvm::ConstantInt::get(baseTy, width - 1);
            shift = builder.CreateSub(lv, w);
            break;
        }
    }

    auto shiftedV = builder.CreateLShr(vBase, shift);
    auto shiftedU = builder.CreateLShr(uBase, shift);

    unsigned baseBits = baseTy->getIntegerBitWidth();
    auto maskInt = llvm::APInt::getLowBitsSet(baseBits, width);
    auto maskConst = llvm::ConstantInt::get(baseTy, maskInt);

    auto extractedV = builder.CreateAnd(shiftedV, maskConst);
    auto extractedU = builder.CreateAnd(shiftedU, maskConst);

    // Resize to result type.
    auto resultTy = builder.types.twoStateFor(e.type->getBitWidth());
    if (extractedV->getType() != resultTy) {
        unsigned resultBits = resultTy->getIntegerBitWidth();
        if (extractedV->getType()->getIntegerBitWidth() > resultBits) {
            extractedV = builder.CreateTrunc(extractedV, resultTy);
            extractedU = builder.CreateTrunc(extractedU, resultTy);
        }
        else {
            extractedV = builder.CreateZExt(extractedV, resultTy);
            extractedU = builder.CreateZExt(extractedU, resultTy);
        }
    }

    if (!e.type->isFourState())
        return extractedV;
    return builder.createSVInt(extractedV, extractedU, ty);
}

llvm::Value* ExprEmitter::visit(const MemberAccessExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const CallExpression& e) {
    if (e.isSystemCall())
        return fe.emitSysCall(e);

    const auto sub = std::get<const SubroutineSymbol*>(e.subroutine);

    llvm::Function* callee = nullptr;
    if (auto it = fe.context.funcMap.find(sub); it != fe.context.funcMap.end()) {
        callee = it->second;
    }
    else {
        FunctionEmitter inner(fe.context);
        callee = inner.lower(*sub);
    }

    SmallVector<llvm::Value*, 8> args;
    for (auto argExpr : e.arguments())
        args.push_back(fe.emitExpr(*argExpr));

    return builder.CreateCall(callee, args);
}

llvm::Value* ExprEmitter::visit(const DataTypeExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const TypeReferenceExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const ArbitrarySymbolExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const LValueReferenceExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const SimpleAssignmentPatternExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const StructuredAssignmentPatternExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const ReplicatedAssignmentPatternExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const EmptyArgumentExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const ValueRangeExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const DistExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const NewArrayExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const NewClassExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const NewCovergroupExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const CopyClassExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const MinTypMaxExpression& e) {
    return fe.emitExpr(e.selected());
}

llvm::Value* ExprEmitter::visit(const ClockingEventExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const AssertionInstanceExpression&) {
    SLANG_UNIMPLEMENTED;
}

llvm::Value* ExprEmitter::visit(const TaggedUnionExpression&) {
    SLANG_UNIMPLEMENTED;
}

} // anonymous namespace

llvm::Value* FunctionEmitter::emitLValue(const Expression& expr) {
    return expr.visit(LValueVisitor{*this});
}

llvm::Value* FunctionEmitter::emitCond(const Expression& expr) {
    auto v = emitExpr(expr);
    auto ty = v->getType();

    // Already i1 (e.g. from a comparison that was already reduced).
    if (ty->isIntegerTy(1))
        return v;

    if (expr.type->isFourState()) {
        auto val = builder.getValPart(v);
        auto unk = builder.getUnkPart(v);
        auto iN = val->getType();
        auto zero = llvm::ConstantInt::get(iN, 0);
        auto noUnk = builder.CreateICmpEQ(unk, zero);
        auto nonZero = builder.CreateICmpNE(val, zero);
        return builder.CreateAnd(noUnk, nonZero);
    }

    if (ty->isIntegerTy()) {
        auto zero = llvm::ConstantInt::get(ty, 0);
        return builder.CreateICmpNE(v, zero);
    }

    if (ty->isFloatingPointTy()) {
        auto zero = llvm::ConstantFP::get(ty, 0.0);
        return builder.CreateFCmpONE(v, zero);
    }

    return builder.CreateICmpNE(v, llvm::Constant::getNullValue(ty));
}

llvm::Value* FunctionEmitter::emitExpr(const Expression& expr) {
    return expr.visit(ExprEmitter{*this});
}

llvm::Value* FunctionEmitter::emitConversion(llvm::Value* val, const Type& fromType,
                                             const Type& toType, ConversionKind conversionKind,
                                             bool forceFloatTrunc) {
    return ExprEmitter{*this}.emitConversion(val, fromType, toType, conversionKind,
                                             forceFloatTrunc);
}

} // namespace slang::codegen
