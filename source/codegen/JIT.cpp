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
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/TargetSelect.h>

#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/codegen/CodeGenerator.h"

namespace slang::codegen {

using namespace ast;

class JIT::Impl {
public:
    std::unique_ptr<llvm::orc::LLJIT> lljit;
    Compilation& compilation;

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

    // Functions are emitted with PrivateLinkage so they don't leak across
    // compilation units. Promote them to ExternalLinkage so LLJIT can
    // export them into its symbol table and make them reachable via lookup().
    for (auto& fn : *ctx.module) {
        if (fn.hasPrivateLinkage() || fn.hasInternalLinkage())
            fn.setLinkage(llvm::GlobalValue::ExternalLinkage);
    }

    llvm::orc::ThreadSafeContext tsCtx(std::move(ctx.ctx));
    llvm::orc::ThreadSafeModule tsModule(std::move(ctx.module), tsCtx);

    if (auto err = (*jitOrErr)->addIRModule(std::move(tsModule)))
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    JIT result;
    result.impl = std::make_unique<Impl>(ctx.compilation);
    result.impl->lljit = std::move(*jitOrErr);
    return result;
}

nonstd::expected<void*, std::string> JIT::lookup(std::string_view name) {
    auto sym = impl->lljit->lookup(name);
    if (auto err = sym.takeError())
        return nonstd::make_unexpected(llvm::toString(std::move(err)));

    return reinterpret_cast<void*>(sym->getValue());
}

nonstd::expected<std::string, std::string> JIT::runFunction(std::string_view funcName) {
    // Find the subroutine in the compiled units to validate its signature.
    const SubroutineSymbol* target = nullptr;
    for (auto unit : impl->compilation.getCompilationUnits()) {
        auto sym = unit->find(funcName);
        if (sym && sym->kind == SymbolKind::Subroutine) {
            target = &sym->as<SubroutineSymbol>();
            break;
        }
    }

    if (!target) {
        return nonstd::make_unexpected(
            fmt::format("function '{}' not found in compiled sources", funcName));
    }

    if (!target->getArguments().empty()) {
        return nonstd::make_unexpected(
            fmt::format("'{}' has {} argument(s)\n", funcName, target->getArguments().size()));
    }

    auto& retType = target->getReturnType();
    const bool returnTypeOK = retType.isVoid() || retType.isFloating() ||
                              (retType.isIntegral() && retType.getBitWidth() <= 64 &&
                               (!retType.isFourState() || retType.getBitWidth() <= 32));

    if (!returnTypeOK) {
        return nonstd::make_unexpected(
            fmt::format("'{}' returns '{}'\n", funcName, retType.toString()));
    }

    auto fnOrErr = lookup(funcName);
    if (!fnOrErr)
        return fnOrErr.error();

    void* fnPtr = *fnOrErr;
    if (retType.isVoid()) {
        reinterpret_cast<void (*)()>(fnPtr)();
        return "";
    }
    else if (retType.isFloating()) {
        if (retType.getBitWidth() == 32)
            return fmt::to_string(reinterpret_cast<float (*)()>(fnPtr)());
        else
            return fmt::to_string(reinterpret_cast<double (*)()>(fnPtr)());
    }
    else {
        // Sort of hacky interpretation of integral return type, since we aren't
        // fully ABI compatible in the code generator.
        bitwidth_t width = retType.getBitWidth();
        if (retType.isFourState())
            width *= 2;

        auto makeResult = [&](auto&& val) {
            const bool isSigned = std::is_signed_v<std::decay_t<decltype(val)>>;
            if (!retType.isFourState())
                return SVInt(width, uint64_t(val), isSigned).toString();

            auto w = retType.getBitWidth();
            if ((val >> w) == 0)
                return SVInt(w, uint64_t(val), isSigned).toString();

            uint64_t arr[] = {uint64_t(val) & ((1ull << w) - 1), uint64_t(val) >> w};
            SVIntStorage storage(arr, w, isSigned, true);
            return SVInt(storage).toString();
        };

#define CALL(t) return makeResult(reinterpret_cast<t (*)()>(fnPtr)())

        if (retType.isSigned()) {
            if (width <= 8)
                CALL(int8_t);
            else if (width <= 16)
                CALL(int16_t);
            else if (width <= 32)
                CALL(int32_t);
            else
                CALL(int64_t);
        }
        else {
            if (width <= 8)
                CALL(uint8_t);
            else if (width <= 16)
                CALL(uint16_t);
            else if (width <= 32)
                CALL(uint32_t);
            else
                CALL(uint64_t);
        }
    }

    SLANG_UNREACHABLE;
}

} // namespace slang::codegen
