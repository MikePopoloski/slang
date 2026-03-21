//------------------------------------------------------------------------------
// JIT.cpp
// LLVM-based JIT compilation for SystemVerilog subroutines.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/codegen/JIT.h"

#include "CodegenImpl.h"
#include <fmt/format.h>
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/TargetSelect.h>

#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"
#include "slang/codegen/CodeGenerator.h"
#include "slang/numeric/SVInt.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang::codegen {

using namespace ast;

class JIT::Impl {
public:
    std::unique_ptr<llvm::orc::LLJIT> lljit;
    Compilation& compilation;
    int trampolineCount = 0;

    Impl(Compilation& compilation) : compilation(compilation) {}
};

JIT::JIT() = default;
JIT::~JIT() = default;
JIT::JIT(JIT&&) noexcept = default;
JIT& JIT::operator=(JIT&&) noexcept = default;

nonstd::expected<JIT, std::string> JIT::create(CodeGenerator&& gen) {
    // Build the LLJIT instance targeting the current process.
    auto jitOrErr = llvm::orc::LLJITBuilder().create();
    if (auto err = jitOrErr.takeError())
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    // Transfer the LLVM context and module out of the CodeGenerator.
    // After this point gen must not be used.
    CodegenContext& ctx = gen.impl->context;

    llvm::orc::ThreadSafeContext tsCtx(std::move(ctx.ctx));
    llvm::orc::ThreadSafeModule tsModule(std::move(ctx.module), tsCtx);

    if (auto err = (*jitOrErr)->addIRModule(std::move(tsModule)))
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    JIT result;
    result.impl = std::make_unique<Impl>(ctx.compilation);
    result.impl->lljit = std::move(*jitOrErr);
    return result;
}

static llvm::Type* dpiArgIRType(llvm::LLVMContext& ctx, const Type& ty) {
    // Pointer-passed types cannot be represented as inline constant values in trampolines.
    auto t = TypeEmitter::lowerForDPIArg(ctx, ty);
    if (!t || t->isPointerTy())
        return nullptr;
    return t;
}

// Create an LLVM constant suitable for passing a ConstantValue as a DPI argument.
// Returns nullptr if the combination is not supported.
static llvm::Constant* makeDPIArgConstant(llvm::LLVMContext& ctx, const ConstantValue& val,
                                          const Type& ty) {
    auto llvmTy = dpiArgIRType(ctx, ty);
    if (!llvmTy || llvmTy->isVoidTy())
        return nullptr;

    auto& ct = ty.getCanonicalType();
    if (ct.isFloating()) {
        double d;
        if (val.isReal())
            d = val.real().v;
        else if (val.isShortReal())
            d = static_cast<double>(val.shortReal().v);
        else if (val.isInteger())
            d = val.integer().toDouble();
        else
            return nullptr;
        return llvm::ConstantFP::get(llvmTy, d);
    }

    if (!val.isInteger())
        return nullptr;

    uint64_t raw = val.integer().getRawPtr()[0];
    return llvm::ConstantInt::get(llvmTy, raw);
}

nonstd::expected<void*, std::string> JIT::lookup(std::string_view name) {
    auto sym = impl->lljit->lookup(name);
    if (auto err = sym.takeError())
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    return reinterpret_cast<void*>(sym->getValue());
}

std::string JIT::linkLibrary(const std::filesystem::path& path) {
    std::string pathStr = getU8Str(path);

    // Determine the file type from its extension.
    auto ext = getU8Str(path.extension());
    strToLower(ext);

    if (ext == ".o" || ext == ".obj") {
        // Native object file (.o on Unix, .obj on Windows): load into a MemoryBuffer
        // and add to the JIT.
        auto bufOrErr = llvm::MemoryBuffer::getFile(pathStr);
        if (auto ec = bufOrErr.getError())
            return ec.message();

        if (auto err = impl->lljit->addObjectFile(std::move(*bufOrErr)))
            return llvm::toString(std::move(err));
    }
    else if (ext == ".bc") {
        // LLVM bitcode: parse into a Module and add as an IR module.
        auto bufOrErr = llvm::MemoryBuffer::getFile(pathStr);
        if (auto ec = bufOrErr.getError())
            return ec.message();

        // Each IR module must have its own LLVMContext for thread safety.
        auto ctx = std::make_unique<llvm::LLVMContext>();
        auto modOrErr = llvm::parseBitcodeFile((*bufOrErr)->getMemBufferRef(), *ctx);
        if (auto err = modOrErr.takeError())
            return llvm::toString(std::move(err));

        llvm::orc::ThreadSafeContext tsc(std::move(ctx));
        llvm::orc::ThreadSafeModule tsm(std::move(*modOrErr), tsc);
        if (auto err = impl->lljit->addIRModule(std::move(tsm)))
            return llvm::toString(std::move(err));
    }
    else if (ext == ".a" || ext == ".lib") {
        // Static archive: use LLJIT's built-in StaticLibraryDefinitionGenerator.
        if (auto err = impl->lljit->linkStaticLibraryInto(impl->lljit->getMainJITDylib(),
                                                          pathStr.c_str())) {
            return llvm::toString(std::move(err));
        }
    }
    else if (ext == ".so" || ext == ".dll" || ext == ".dylib") {
        // Shared/dynamic library: load it and add it to the main dylib's link order
        // so that symbols are resolved when the JIT module is finalized.
        auto dynLibOrErr = impl->lljit->loadPlatformDynamicLibrary(pathStr.c_str());
        if (auto err = dynLibOrErr.takeError())
            return llvm::toString(std::move(err));

        impl->lljit->getMainJITDylib().addToLinkOrder(*dynLibOrErr);
    }
    else {
        return fmt::format("unrecognized extension '{}'; expected .o, .obj, .bc, .a, .lib, "
                           ".so, .dll, or .dylib",
                           ext);
    }

    return {};
}

nonstd::expected<ConstantValue, std::string> JIT::runFunction(std::string_view funcName,
                                                              std::span<const ConstantValue> args) {
    // Find the DPI export whose C identifier matches funcName.
    const SubroutineSymbol* target = nullptr;
    for (auto& [sub, cIdent] : impl->compilation.getDPIExports()) {
        if (cIdent == funcName) {
            target = sub;
            break;
        }
    }

    if (!target) {
        return nonstd::make_unexpected(
            fmt::format("no DPI export named '{}' found in compiled sources", funcName));
    }

    auto funcArgs = target->getArguments();
    if (funcArgs.size() != args.size()) {
        return nonstd::make_unexpected(
            fmt::format("'{}' expects {} argument(s) but {} were provided\n", funcName,
                        funcArgs.size(), args.size()));
    }

    // Only simple return types are callable via runFunction.
    auto& retType = target->getReturnType();
    const auto& retCt = retType.getCanonicalType();
    if (!retType.isValidForDPIReturn()) {
        return nonstd::make_unexpected(
            fmt::format("'{}' returns '{}'\n", funcName, retType.toString()));
    }

    // Look up the callable: either the exported function directly (0 args) or a
    // trampoline that hard-codes the arguments as LLVM constants and returns the
    // same type as the original (> 0 args).
    std::string lookupName(funcName);
    if (!args.empty()) {
        auto nameOrErr = createTrampoline(funcName, *target, args);
        if (!nameOrErr)
            return nonstd::make_unexpected(nameOrErr.error());
        lookupName = *nameOrErr;
    }

    auto fnOrErr = lookup(lookupName);
    if (!fnOrErr)
        return nonstd::make_unexpected(fnOrErr.error());
    auto fnPtr = *fnOrErr;

    if (retCt.isVoid()) {
        reinterpret_cast<void (*)()>(fnPtr)();
        return ConstantValue{};
    }

    if (retCt.isFloating()) {
        if (retCt.getBitWidth() == 32) {
            float v = reinterpret_cast<float (*)()>(fnPtr)();
            return ConstantValue(shortreal_t(v));
        }
        else {
            double v = reinterpret_cast<double (*)()>(fnPtr)();
            return ConstantValue(real_t(v));
        }
    }

    // Integral types: DPI ABI maps scalars (bit/logic) to i8 (svBit/svLogic),
    // and predefined integers to their natural C widths.
    if (retCt.kind == SymbolKind::ScalarType) {
        // DPI returns svBit (0/1) or svLogic (0/1/2/3) as uint8_t.
        uint8_t sv = reinterpret_cast<uint8_t (*)()>(fnPtr)();
        const bool isFourState = retCt.isFourState();
        if (!isFourState) {
            // 2-state: just the bit value.
            return ConstantValue(SVInt(1, sv & 1u, false));
        }

        // 4-state: svLogic encoding: bit0=val, bit1=unk.
        uint64_t valBit = sv & 1u;
        uint64_t unkBit = (sv >> 1) & 1u;
        if (unkBit == 0)
            return ConstantValue(SVInt(1, valBit, false));

        uint64_t arr[] = {valBit, unkBit};
        SVIntStorage storage(arr, 1, false, /* hasUnknown */ true);
        return ConstantValue(SVInt(storage));
    }

    // PredefinedIntegerType: call with the appropriate C type and build SVInt.
    SLANG_ASSERT(retCt.kind == SymbolKind::PredefinedIntegerType);
    auto& pit = retCt.as<PredefinedIntegerType>();
    const bool isSigned = retCt.isSigned();

#define CALL_INT(ctype, width, signFlag)                                        \
    do {                                                                        \
        ctype v = reinterpret_cast<ctype (*)()>(fnPtr)();                       \
        return ConstantValue(SVInt(width, static_cast<uint64_t>(v), signFlag)); \
    } while (0)

    switch (pit.integerKind) {
        case PredefinedIntegerType::Byte:
            if (isSigned)
                CALL_INT(int8_t, 8, true);
            else
                CALL_INT(uint8_t, 8, false);
        case PredefinedIntegerType::ShortInt:
            if (isSigned)
                CALL_INT(int16_t, 16, true);
            else
                CALL_INT(uint16_t, 16, false);
        case PredefinedIntegerType::Int:
            if (isSigned)
                CALL_INT(int32_t, 32, true);
            else
                CALL_INT(uint32_t, 32, false);
        case PredefinedIntegerType::LongInt:
            if (isSigned)
                CALL_INT(int64_t, 64, true);
            else
                CALL_INT(uint64_t, 64, false);
        default:
            SLANG_UNREACHABLE;
    }
#undef CALL_INT
    SLANG_UNREACHABLE;
}

nonstd::expected<std::string, std::string> JIT::createTrampoline(
    std::string_view funcName, const SubroutineSymbol& target,
    std::span<const ConstantValue> args) {

    // Build a small LLVM module with a zero-argument trampoline that calls the
    // target with constant arguments and forwards its return value.
    auto trampoCtx = std::make_unique<llvm::LLVMContext>();
    auto trampoModule = std::make_unique<llvm::Module>("__trampoline__", *trampoCtx);
    llvm::IRBuilder<> builder(*trampoCtx);

    // Collect LLVM arg types and constant values.
    SmallVector<llvm::Type*, 8> paramTypes;
    SmallVector<llvm::Value*, 8> argConsts;
    auto formalArgs = target.getArguments();
    for (size_t i = 0; i < args.size(); i++) {
        auto c = makeDPIArgConstant(*trampoCtx, args[i], formalArgs[i]->getType());
        if (!c) {
            return nonstd::make_unexpected(
                fmt::format("argument {} has an unsupported DPI type for '{}'", i, funcName));
        }
        paramTypes.push_back(c->getType());
        argConsts.push_back(c);
    }

    // Determine the return type in LLVM IR.
    auto& retType = target.getReturnType();
    auto retLlvmTy = dpiArgIRType(*trampoCtx, retType);
    if (!retLlvmTy) {
        return nonstd::make_unexpected(
            fmt::format("'{}' has an unsupported DPI return type", funcName));
    }

    // Declare the target function as an external symbol.
    auto targetFnTy = llvm::FunctionType::get(retLlvmTy, paramTypes, false);
    auto targetDecl = llvm::Function::Create(targetFnTy, llvm::Function::ExternalLinkage,
                                             std::string(funcName), trampoModule.get());

    // Create the zero-argument trampoline.
    std::string trampoName = fmt::format("__run_trampoline_{}__", impl->trampolineCount++);
    auto trampoFnTy = llvm::FunctionType::get(retLlvmTy, {}, false);
    auto trampoline = llvm::Function::Create(trampoFnTy, llvm::Function::ExternalLinkage,
                                             trampoName, trampoModule.get());

    auto entry = llvm::BasicBlock::Create(*trampoCtx, "entry", trampoline);
    builder.SetInsertPoint(entry);

    auto callResult = builder.CreateCall(targetFnTy, targetDecl, argConsts);
    if (retLlvmTy->isVoidTy())
        builder.CreateRetVoid();
    else
        builder.CreateRet(callResult);

    // Verify and add to the JIT.
    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    if (llvm::verifyModule(*trampoModule, &errOS))
        return nonstd::make_unexpected(fmt::format("trampoline IR error: {}", errStr));

    llvm::orc::ThreadSafeContext tsc(std::move(trampoCtx));
    llvm::orc::ThreadSafeModule tsm(std::move(trampoModule), tsc);
    if (auto err = impl->lljit->addIRModule(std::move(tsm)))
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    return trampoName;
}

} // namespace slang::codegen
