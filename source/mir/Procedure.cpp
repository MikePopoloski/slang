//------------------------------------------------------------------------------
// Procedure.cpp
// MIR procedures (always, initial, etc)
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/mir/Procedure.h"

#include "slang/binding/Statements.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/mir/MIRBuilder.h"
#include "slang/mir/MIRPrinter.h"
#include "slang/symbols/ASTVisitor.h"

namespace {

using namespace slang;
using namespace slang::mir;

class ProcedureVisitor {
public:
    Procedure& proc;
    EvalContext evalCtx;

    ProcedureVisitor(Procedure& proc) :
        proc(proc), evalCtx(proc.getCompilation(), EvalFlags::CacheResults) {}

    void visit(const EmptyStatement&) {}
    void visit(const StatementList& list) {
        for (auto stmt : list.list)
            stmt->visit(*this);
    }

    void visit(const BlockStatement& block) { block.getStatements().visit(*this); }
    void visit(const ExpressionStatement& stmt) { stmt.expr.visit(*this); }

    void visit(const VariableDeclStatement& stmt) {
        if (stmt.symbol.lifetime == VariableLifetime::Automatic)
            proc.emitLocal(stmt.symbol);
        else
            proc.emitGlobal(stmt.symbol);
    }

    void visit(const ReturnStatement&) {}
    void visit(const BreakStatement&) {}
    void visit(const ContinueStatement&) {}
    void visit(const DisableStatement&) {}
    void visit(const ConditionalStatement&) {}
    void visit(const CaseStatement&) {}
    void visit(const ForLoopStatement&) {}
    void visit(const RepeatLoopStatement&) {}
    void visit(const ForeachLoopStatement&) {}
    void visit(const WhileLoopStatement&) {}
    void visit(const DoWhileLoopStatement&) {}
    void visit(const ForeverLoopStatement&) {}
    void visit(const TimedStatement&) {}
    void visit(const ImmediateAssertionStatement&) {}
    void visit(const ConcurrentAssertionStatement&) {}
    void visit(const DisableForkStatement&) {}
    void visit(const WaitStatement&) {}
    void visit(const WaitForkStatement&) {}
    void visit(const WaitOrderStatement&) {}
    void visit(const EventTriggerStatement&) {}
    void visit(const ProceduralAssignStatement&) {}
    void visit(const ProceduralDeassignStatement&) {}
    void visit(const RandCaseStatement&) {}
    void visit(const RandSequenceStatement&) {}

    MIRValue visit(const IntegerLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const RealLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const TimeLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const UnbasedUnsizedIntegerLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const NullLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const UnboundedLiteral& expr) { return emitConst(expr); }
    MIRValue visit(const StringLiteral& expr) { return emitConst(expr); }

    MIRValue visit(const NamedValueExpression& expr) {
        // Some symbols are always constants, so just eval those.
        if (expr.symbol.kind == SymbolKind::Parameter || expr.symbol.kind == SymbolKind::EnumValue)
            return emitConst(expr);

        // Either we find this in our locals map, or we assume it's a global
        // declared somewhere else. emitGlobal will check first if we've
        // already allocated a slot, so it's fine to just call it as-is.
        // TODO: handle non-variable references
        auto& var = expr.symbol.as<VariableSymbol>();
        if (auto localSlot = proc.findLocalSlot(var))
            return localSlot;
        return proc.emitGlobal(var);
    }

    MIRValue visit(const HierarchicalValueExpression&) { return {}; }

    MIRValue visit(const UnaryExpression& expr) {
        MIRValue val = expr.operand().visit(*this);
        if (val.isConstant())
            return emitConst(expr);

#define INSTR(x) proc.emitInstr(InstrKind::x, *expr.type, val)
        switch (expr.op) {
            case UnaryOperator::Plus:
                return val;
            case UnaryOperator::Minus:
                return INSTR(negate);
            case UnaryOperator::BitwiseNot:
                return INSTR(bitnot);
            case UnaryOperator::BitwiseAnd:
                return INSTR(reducand);
            case UnaryOperator::BitwiseOr:
                return INSTR(reducor);
            case UnaryOperator::BitwiseXor:
                return INSTR(reducxor);
            case UnaryOperator::BitwiseNand:
                val = INSTR(reducand);
                return INSTR(bitnot);
            case UnaryOperator::BitwiseNor:
                val = INSTR(reducor);
                return INSTR(bitnot);
            case UnaryOperator::BitwiseXnor:
                val = INSTR(reducxor);
                return INSTR(bitnot);
            case UnaryOperator::LogicalNot:
            case UnaryOperator::Preincrement:
            case UnaryOperator::Predecrement:
            case UnaryOperator::Postincrement:
            case UnaryOperator::Postdecrement:
                // TODO:
                break;
        }
#undef INSTR

        return {};
    }

    MIRValue visit(const BinaryExpression&) { return {}; }
    MIRValue visit(const ConditionalExpression&) { return {}; }
    MIRValue visit(const InsideExpression&) { return {}; }
    MIRValue visit(const AssignmentExpression&) { return {}; }
    MIRValue visit(const ConcatenationExpression&) { return {}; }
    MIRValue visit(const ReplicationExpression&) { return {}; }
    MIRValue visit(const StreamingConcatenationExpression&) { return {}; }
    MIRValue visit(const ElementSelectExpression&) { return {}; }
    MIRValue visit(const RangeSelectExpression&) { return {}; }
    MIRValue visit(const MemberAccessExpression&) { return {}; }

    MIRValue visit(const CallExpression& expr) {
        if (expr.isSystemCall()) {
            std::get<1>(expr.subroutine).subroutine->lower(proc, expr.arguments());
            return {};
        }
        return {};
    }

    MIRValue visit(const ConversionExpression&) { return {}; }
    MIRValue visit(const NewArrayExpression&) { return {}; }
    MIRValue visit(const NewClassExpression&) { return {}; }
    MIRValue visit(const CopyClassExpression&) { return {}; }
    MIRValue visit(const MinTypMaxExpression&) { return {}; }
    MIRValue visit(const DataTypeExpression&) { return {}; }
    MIRValue visit(const TypeReferenceExpression&) { return {}; }
    MIRValue visit(const HierarchicalReferenceExpression&) { return {}; }
    MIRValue visit(const LValueReferenceExpression&) { return {}; }
    MIRValue visit(const SimpleAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const StructuredAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const ReplicatedAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const EmptyArgumentExpression&) { return {}; }
    MIRValue visit(const OpenRangeExpression&) { return {}; }
    MIRValue visit(const DistExpression&) { return {}; }
    MIRValue visit(const ClockingEventExpression&) { return {}; }
    MIRValue visit(const AssertionInstanceExpression&) { return {}; }
    MIRValue visit(const TaggedUnionExpression&) { return {}; }

    void visitInvalid(const Statement&) {}
    MIRValue visitInvalid(const Expression&) { return {}; }

private:
    MIRValue emitConst(const Expression& expr) {
        return proc.emitConst(*expr.type, expr.eval(evalCtx));
    }
};

} // namespace

namespace slang::mir {

Procedure::Procedure(MIRBuilder& builder, const ProceduralBlockSymbol& procedure) :
    builder(builder) {
    ProcedureVisitor visitor(*this);
    procedure.getBody().visit(visitor);
}

MIRValue Procedure::emitExpr(const Expression& expr) {
    ProcedureVisitor visitor(*this);
    return expr.visit(visitor);
}

MIRValue Procedure::emitCall(SysCallKind sysCall, const Type& returnType,
                             span<const MIRValue> args) {
    instructions.emplace_back(sysCall, returnType, copyValues(args));
    return MIRValue::slot(instructions.size() - 1);
}

void Procedure::emitCall(SysCallKind sysCall, span<const MIRValue> args) {
    emitCall(sysCall, builder.compilation.getVoidType(), args);
}

void Procedure::emitCall(SysCallKind sysCall, MIRValue arg0) {
    emitCall(sysCall, { &arg0, 1 });
}

MIRValue Procedure::emitInstr(InstrKind kind, const Type& type, MIRValue op0) {
    instructions.emplace_back(kind, type, op0);
    return MIRValue::slot(instructions.size() - 1);
}

MIRValue Procedure::emitInstr(InstrKind kind, const Type& type, MIRValue op0, MIRValue op1) {
    instructions.emplace_back(kind, type, op0, op1);
    return MIRValue::slot(instructions.size() - 1);
}

MIRValue Procedure::emitInt(bitwidth_t width, uint64_t value, bool isSigned) {
    bitmask<IntegralFlags> flags = IntegralFlags::TwoState;
    if (isSigned)
        flags |= IntegralFlags::Signed;

    return emitConst(getCompilation().getType(width, flags), SVInt(width, value, isSigned));
}

MIRValue Procedure::emitString(std::string&& str) {
    return emitConst(getCompilation().getStringType(), ConstantValue(std::move(str)));
}

void Procedure::emitLocal(const VariableSymbol& symbol) {
    ASSERT(symbol.lifetime == VariableLifetime::Automatic);
    auto val = MIRValue::local(locals.size());
    localMap.emplace(&symbol, val);
    locals.push_back(&symbol);

    if (auto init = symbol.getInitializer()) {
        auto iv = emitExpr(*init);
        instructions.emplace_back(InstrKind::store, symbol.getType(), val, iv);
    }
}

const VariableSymbol& Procedure::getLocalSymbol(MIRValue val) const {
    ASSERT(val.getKind() == MIRValue::Local);
    return *locals[val.asIndex()];
}

MIRValue Procedure::findLocalSlot(const VariableSymbol& symbol) const {
    if (auto it = localMap.find(&symbol); it != localMap.end())
        return it->second;
    return MIRValue();
}

Compilation& Procedure::getCompilation() const {
    return builder.compilation;
}

std::string Procedure::toString() const {
    return MIRPrinter(builder).print(*this).str();
}

span<const MIRValue> Procedure::copyValues(span<const MIRValue> values) {
    if (values.empty())
        return {};

    size_t bytes = sizeof(MIRValue) * values.size();
    auto data = (MIRValue*)builder.allocate(bytes, alignof(MIRValue));
    memcpy(data, values.data(), bytes);

    return { data, values.size() };
}

} // namespace slang::mir
