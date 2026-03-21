//------------------------------------------------------------------------------
// SysCallEmitter.cpp
// Emission of built-in SystemVerilog system calls to LLVM IR.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "CodegenImpl.h"
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Intrinsics.h>

#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/types/Type.h"
#include "slang/parsing/KnownSystemName.h"

namespace slang::codegen {

namespace {

using KSN = parsing::KnownSystemName;

struct SysCallEmitter {
    FunctionEmitter& fe;
    IRBuilder& builder;

    explicit SysCallEmitter(FunctionEmitter& fe) : fe(fe), builder(fe.builder) {}

    llvm::Value* emit(const CallExpression& e);

private:
    llvm::Value* arg0(const CallExpression& e) {
        SLANG_ASSERT(e.arguments().size() == 1);
        return fe.emitExpr(*e.arguments()[0]);
    }

    llvm::FunctionCallee declareExternFn(std::string_view name, llvm::FunctionType* ty) {
        return fe.context.module->getOrInsertFunction(name, ty);
    }

    llvm::Value* emitUnaryF64Intrinsic(llvm::Intrinsic::ID id, const CallExpression& e);
    llvm::Value* emitBinaryF64Intrinsic(llvm::Intrinsic::ID id, const CallExpression& e);
    llvm::Value* emitUnaryLibmF64(std::string_view name, const CallExpression& e);
    llvm::Value* emitBinaryLibmF64(std::string_view name, const CallExpression& e);

    llvm::Value* emitClog2(llvm::Value* val, bool fourState);
};

llvm::Value* SysCallEmitter::emit(const CallExpression& e) {
    auto& comp = fe.context.compilation;
    switch (e.getKnownSystemName()) {
        // ----------------------------------------------------------------
        // Type/dimension query functions
        // These are typically constant-folded during elaboration; they
        // require special handling if they survive to codegen.
        // ----------------------------------------------------------------
        case KSN::Bits:
        case KSN::Typename:
        case KSN::IsUnbounded:
        case KSN::IsUnknown:
        case KSN::Low:
        case KSN::High:
        case KSN::Left:
        case KSN::Right:
        case KSN::Size:
        case KSN::Increment:
        case KSN::Dimensions:
        case KSN::UnpackedDimensions:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Conversion functions
        // ----------------------------------------------------------------
        case KSN::Rtoi:
            // Like a normal real to int conversion but no rounding.
            return fe.emitConversion(arg0(e), comp.getRealType(), comp.getIntegerType(),
                                     ConversionKind::Explicit, /* forceFloatTrunc */ true);
        case KSN::Itor:
            return fe.emitConversion(arg0(e), *e.arguments()[0]->type, comp.getRealType(),
                                     ConversionKind::Explicit);
        case KSN::RealToBits:
            return builder.CreateBitCast(arg0(e), builder.types.Int64Ty);
        case KSN::BitsToReal:
            return builder.CreateBitCast(arg0(e), builder.types.DoubleTy);
        case KSN::ShortrealToBits:
            return builder.CreateBitCast(arg0(e), builder.types.Int32Ty);
        case KSN::BitsToShortreal:
            return builder.CreateBitCast(arg0(e), builder.types.FloatTy);
        case KSN::Cast:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Integer math functions
        // ----------------------------------------------------------------
        case KSN::Clog2:
            return emitClog2(arg0(e), e.arguments()[0]->type->isFourState());
        case KSN::CountBits:
        case KSN::CountOnes:
        case KSN::OneHot:
        case KSN::OneHot0:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Floating-point math functions — LLVM intrinsics
        // ----------------------------------------------------------------
        case KSN::Ln:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::log, e);
        case KSN::Log10:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::log10, e);
        case KSN::Exp:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::exp, e);
        case KSN::Sqrt:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::sqrt, e);
        case KSN::Floor:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::floor, e);
        case KSN::Ceil:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::ceil, e);
        case KSN::Sin:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::sin, e);
        case KSN::Cos:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::cos, e);
        case KSN::Tan:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::tan, e);
        case KSN::Asin:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::asin, e);
        case KSN::Acos:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::acos, e);
        case KSN::Atan:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::atan, e);
        case KSN::Sinh:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::sinh, e);
        case KSN::Cosh:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::cosh, e);
        case KSN::Tanh:
            return emitUnaryF64Intrinsic(llvm::Intrinsic::tanh, e);
        case KSN::Atan2:
            return emitBinaryF64Intrinsic(llvm::Intrinsic::atan2, e);
        case KSN::Pow:
            return emitBinaryF64Intrinsic(llvm::Intrinsic::pow, e);

        // ----------------------------------------------------------------
        // Floating-point math functions — C library (no LLVM intrinsic)
        // ----------------------------------------------------------------
        case KSN::Asinh:
            return emitUnaryLibmF64("asinh"sv, e);
        case KSN::Acosh:
            return emitUnaryLibmF64("acosh"sv, e);
        case KSN::Atanh:
            return emitUnaryLibmF64("atanh"sv, e);
        case KSN::Hypot:
            return emitBinaryLibmF64("hypot"sv, e);

        // ----------------------------------------------------------------
        // Time functions
        // ----------------------------------------------------------------
        case KSN::Time:
        case KSN::STime:
        case KSN::RealTime:
        case KSN::TimeUnit:
        case KSN::TimePrecision:
        case KSN::TimeFormat:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Severity tasks
        // ----------------------------------------------------------------
        case KSN::Info:
        case KSN::Warning:
        case KSN::Error:
        case KSN::Fatal:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Display / output tasks
        // ----------------------------------------------------------------
        case KSN::Display:
        case KSN::DisplayB:
        case KSN::DisplayO:
        case KSN::DisplayH:
        case KSN::Write:
        case KSN::WriteB:
        case KSN::WriteO:
        case KSN::WriteH:
        case KSN::Strobe:
        case KSN::StrobeB:
        case KSN::StrobeO:
        case KSN::StrobeH:
        case KSN::Monitor:
        case KSN::MonitorB:
        case KSN::MonitorO:
        case KSN::MonitorH:
        case KSN::FDisplay:
        case KSN::FDisplayB:
        case KSN::FDisplayO:
        case KSN::FDisplayH:
        case KSN::FWrite:
        case KSN::FWriteB:
        case KSN::FWriteO:
        case KSN::FWriteH:
        case KSN::FStrobe:
        case KSN::FStrobeB:
        case KSN::FStrobeO:
        case KSN::FStrobeH:
        case KSN::FMonitor:
        case KSN::FMonitorB:
        case KSN::FMonitorO:
        case KSN::FMonitorH:
        case KSN::SWrite:
        case KSN::SWriteB:
        case KSN::SWriteO:
        case KSN::SWriteH:
        case KSN::SFormat:
        case KSN::PrintTimeScale:
        case KSN::ValuePlusArgs:
        case KSN::SFormatF:
        case KSN::PSPrintF:
        case KSN::TestPlusArgs:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // File I/O tasks and functions
        // ----------------------------------------------------------------
        case KSN::FError:
        case KSN::FGets:
        case KSN::FScanf:
        case KSN::SScanf:
        case KSN::FRead:
        case KSN::FOpen:
        case KSN::FClose:
        case KSN::FGetC:
        case KSN::UngetC:
        case KSN::FTell:
        case KSN::FSeek:
        case KSN::Rewind:
        case KSN::FFlush:
        case KSN::FEof:
        case KSN::ReadMemB:
        case KSN::ReadMemH:
        case KSN::WriteMemB:
        case KSN::WriteMemH:
        case KSN::SReadMemB:
        case KSN::SReadMemH:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Array methods
        // ----------------------------------------------------------------
        case KSN::Reverse:
        case KSN::Delete:
        case KSN::Exists:
        case KSN::Insert:
        case KSN::Index:
        case KSN::Map:
        case KSN::ArraySize:
        case KSN::Or:
        case KSN::And:
        case KSN::XOr:
        case KSN::Sum:
        case KSN::Product:
        case KSN::Find:
        case KSN::FindIndex:
        case KSN::FindFirst:
        case KSN::FindFirstIndex:
        case KSN::FindLast:
        case KSN::FindLastIndex:
        case KSN::Min:
        case KSN::Max:
        case KSN::Unique:
        case KSN::UniqueIndex:
        case KSN::Sort:
        case KSN::Rsort:
        case KSN::Shuffle:
        case KSN::Num:
        case KSN::First:
        case KSN::Last:
        case KSN::Next:
        case KSN::Prev:
        case KSN::PopFront:
        case KSN::PopBack:
        case KSN::PushFront:
        case KSN::PushBack:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // String methods
        // ----------------------------------------------------------------
        case KSN::Name:
        case KSN::Len:
        case KSN::Putc:
        case KSN::Getc:
        case KSN::Substr:
        case KSN::ToUpper:
        case KSN::ToLower:
        case KSN::Compare:
        case KSN::ICompare:
        case KSN::AToI:
        case KSN::AToHex:
        case KSN::AToOct:
        case KSN::AToBin:
        case KSN::AToReal:
        case KSN::IToA:
        case KSN::HexToA:
        case KSN::OctToA:
        case KSN::BinToA:
        case KSN::RealToA:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Constrained randomization
        // ----------------------------------------------------------------
        case KSN::Randomize:
        case KSN::RandMode:
        case KSN::ConstraintMode:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Randomization
        // ----------------------------------------------------------------
        case KSN::Random:
        case KSN::URandom:
        case KSN::URandomRange:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Probability distributions
        // ----------------------------------------------------------------
        case KSN::DistUniform:
        case KSN::DistNormal:
        case KSN::DistExponential:
        case KSN::DistPoisson:
        case KSN::DistChiSquare:
        case KSN::DistT:
        case KSN::DistErlang:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Coverage functions
        // ----------------------------------------------------------------
        case KSN::CoverageControl:
        case KSN::CoverageGetMax:
        case KSN::CoverageGet:
        case KSN::CoverageMerge:
        case KSN::CoverageSave:
        case KSN::GetCoverage:
        case KSN::SetCoverageDbName:
        case KSN::LoadCoverageDb:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Simulator control / PLI tasks
        // ----------------------------------------------------------------
        case KSN::Finish:
        case KSN::Stop:
        case KSN::Exit:
        case KSN::System:
        case KSN::List:
        case KSN::Scope:
        case KSN::MonitorOn:
        case KSN::MonitorOff:
        case KSN::DumpFile:
        case KSN::DumpOn:
        case KSN::DumpOff:
        case KSN::DumpAll:
        case KSN::DumpLimit:
        case KSN::DumpFlush:
        case KSN::DumpPortsOn:
        case KSN::DumpPortsOff:
        case KSN::DumpPortsAll:
        case KSN::DumpPortsLimit:
        case KSN::DumpPortsFlush:
        case KSN::DumpVars:
        case KSN::DumpPorts:
        case KSN::ShowVars:
        case KSN::Input:
        case KSN::Key:
        case KSN::NoKey:
        case KSN::Log:
        case KSN::NoLog:
        case KSN::Reset:
        case KSN::Save:
        case KSN::Restart:
        case KSN::IncSave:
        case KSN::ShowScopes:
        case KSN::ResetCount:
        case KSN::ResetValue:
        case KSN::Scale:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Miscellaneous utility functions
        // ----------------------------------------------------------------
        case KSN::Stacktrace:
        case KSN::CountDrivers:
        case KSN::GetPattern:
        case KSN::SdfAnnotate:
        case KSN::Deposit:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Assertion control tasks
        // ----------------------------------------------------------------
        case KSN::AssertControl:
        case KSN::AssertOn:
        case KSN::AssertOff:
        case KSN::AssertKill:
        case KSN::AssertPassOn:
        case KSN::AssertPassOff:
        case KSN::AssertFailOn:
        case KSN::AssertFailOff:
        case KSN::AssertNonvacuousOn:
        case KSN::AssertVacuousOff:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Sequence / property functions
        // ----------------------------------------------------------------
        case KSN::Triggered:
        case KSN::Matched:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Clocking / temporal functions
        // ----------------------------------------------------------------
        case KSN::Rose:
        case KSN::Fell:
        case KSN::Stable:
        case KSN::Changed:
        case KSN::PastGclk:
        case KSN::RoseGclk:
        case KSN::FellGclk:
        case KSN::StableGclk:
        case KSN::ChangedGclk:
        case KSN::FutureGclk:
        case KSN::RisingGclk:
        case KSN::FallingGclk:
        case KSN::SteadyGclk:
        case KSN::ChangingGclk:
        case KSN::Sampled:
        case KSN::Past:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Queue / PLI tasks
        // ----------------------------------------------------------------
        case KSN::QInitialize:
        case KSN::QAdd:
        case KSN::QRemove:
        case KSN::QExam:
        case KSN::QFull:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Logic array / plane tasks
        // ----------------------------------------------------------------
        case KSN::AsyncAndArray:
        case KSN::SyncAndArray:
        case KSN::AsyncAndPlane:
        case KSN::SyncAndPlane:
        case KSN::AsyncNandArray:
        case KSN::SyncNandArray:
        case KSN::AsyncNandPlane:
        case KSN::SyncNandPlane:
        case KSN::AsyncOrArray:
        case KSN::SyncOrArray:
        case KSN::AsyncOrPlane:
        case KSN::SyncOrPlane:
        case KSN::AsyncNorArray:
        case KSN::SyncNorArray:
        case KSN::AsyncNorPlane:
        case KSN::SyncNorPlane:
            SLANG_UNIMPLEMENTED;

        // ----------------------------------------------------------------
        // Error cases
        // ----------------------------------------------------------------
        case KSN::Unknown:
        case KSN::Signed:
        case KSN::Unsigned:
        case KSN::StaticAssert:
        case KSN::GlobalClock:
        case KSN::InferredClock:
        case KSN::InferredDisable:
            // These should never survive past the elaboration of the AST,
            // because they should always be constant folded or represent
            // an error case or whatever.
            break;
    }
    SLANG_UNREACHABLE;
}

llvm::Value* SysCallEmitter::emitUnaryF64Intrinsic(llvm::Intrinsic::ID id,
                                                   const CallExpression& e) {
    return builder.CreateUnaryIntrinsic(id, arg0(e));
}

llvm::Value* SysCallEmitter::emitBinaryF64Intrinsic(llvm::Intrinsic::ID id,
                                                    const CallExpression& e) {
    auto args = e.arguments();
    SLANG_ASSERT(args.size() == 2);
    auto v0 = fe.emitExpr(*args[0]);
    auto v1 = fe.emitExpr(*args[1]);
    return builder.CreateBinaryIntrinsic(id, v0, v1);
}

llvm::Value* SysCallEmitter::emitUnaryLibmF64(std::string_view name, const CallExpression& e) {
    auto doubleTy = builder.types.DoubleTy;
    auto callee = declareExternFn(name, llvm::FunctionType::get(doubleTy, {doubleTy}, false));
    return builder.CreateCall(callee, {arg0(e)});
}

llvm::Value* SysCallEmitter::emitBinaryLibmF64(std::string_view name, const CallExpression& e) {
    auto doubleTy = builder.types.DoubleTy;
    auto callee = declareExternFn(name,
                                  llvm::FunctionType::get(doubleTy, {doubleTy, doubleTy}, false));

    auto args = e.arguments();
    SLANG_ASSERT(args.size() == 2);
    auto v0 = fe.emitExpr(*args[0]);
    auto v1 = fe.emitExpr(*args[1]);
    return builder.CreateCall(callee, {v0, v1});
}

llvm::Value* SysCallEmitter::emitClog2(llvm::Value* val, bool fourState) {
    // First, if the value is four state, flatten to zeros.
    // Some (but not all) simulators disagree on this and return Xs instead.
    if (fourState) {
        auto [vl, ul] = builder.getIntParts(val);
        val = builder.CreateAnd(vl, builder.CreateNot(ul));
    }

    // $clog2(n) = ceil(log2(n)), with $clog2(0) = 0.
    // Computed as argWidth - ctlz(n-1) for n > 0, handling n=0 separately.
    auto argTy = llvm::cast<llvm::IntegerType>(val->getType());
    auto zero = llvm::ConstantInt::get(argTy, 0);
    auto one = llvm::ConstantInt::get(argTy, 1);
    auto bw = llvm::ConstantInt::get(argTy, argTy->getBitWidth());
    auto nm1 = builder.CreateSub(val, one);
    auto isZero = builder.CreateICmpEQ(val, zero);

    // ctlz(n, IsZeroPoison=true)
    auto ctlzFn = llvm::Intrinsic::getOrInsertDeclaration(fe.context.module.get(),
                                                          llvm::Intrinsic::ctlz, {argTy});
    auto lz = builder.CreateCall(ctlzFn, {nm1, builder.getTrue()});
    auto result = builder.CreateSub(bw, lz);

    // Override the result to 0 when n == 0.
    result = builder.CreateSelect(isZero, zero, result);
    result = builder.CreateZExtOrTrunc(result, builder.types.Int32Ty);

    // Final result is four state, but never unknown.
    return builder.toFourState(result);
}

} // anonymous namespace

llvm::Value* FunctionEmitter::emitSysCall(const CallExpression& e) {
    return SysCallEmitter{*this}.emit(e);
}

} // namespace slang::codegen
