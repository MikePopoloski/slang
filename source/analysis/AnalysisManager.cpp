//------------------------------------------------------------------------------
// AnalysisManager.cpp
// Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalysisManager.h"

#include "slang/ast/ASTDiagMap.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

static const Scope& getAsScope(const Symbol& symbol) {
    switch (symbol.kind) {
        case SymbolKind::Instance: {
            auto& inst = symbol.as<InstanceSymbol>();
            if (auto body = inst.getCanonicalBody())
                return *body;
            return inst.body;
        }
        case SymbolKind::CheckerInstance:
            return symbol.as<CheckerInstanceSymbol>().body;
        default:
            return symbol.as<Scope>();
    }
}

static bool hasUnusedAttrib(const Compilation& compilation, const Symbol& symbol) {
    for (auto attr : compilation.getAttributes(symbol)) {
        if (attr->name == "unused"sv || attr->name == "maybe_unused"sv)
            return attr->getValue().isTrue();
    }
    return false;
}

const AnalyzedScope* PendingAnalysis::tryGet() const {
    return analysisManager->getAnalyzedScope(getAsScope(*symbol));
}

Diagnostic& AnalysisContext::addDiag(const Symbol& symbol, DiagCode code, SourceLocation location) {
    return diagnostics.add(symbol, code, location);
}

Diagnostic& AnalysisContext::addDiag(const Symbol& symbol, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(symbol, code, sourceRange);
}

AnalysisManager::AnalysisManager(bitmask<AnalysisFlags> flags, uint32_t numThreads) :
    analysisFlags(flags), threadPool(numThreads) {

    workerStates.resize(threadPool.get_thread_count() + 1);
}

AnalyzedDesign AnalysisManager::analyze(const Compilation& compilation) {
    SLANG_ASSERT(compilation.isFinalized());
    SLANG_ASSERT(compilation.isFrozen());

    if (compilation.hasFatalErrors())
        return {};

    auto root = compilation.tryGetRoot();
    SLANG_ASSERT(root);

    // Analyze all compilation units first.
    for (auto unit : root->compilationUnits)
        analyzeScopeAsync(*unit);
    wait();

    // Go back through and collect all of the units that were analyzed.
    AnalyzedDesign result(compilation);
    for (auto unit : root->compilationUnits) {
        auto scope = getAnalyzedScope(*unit);
        SLANG_ASSERT(scope);
        result.compilationUnits.push_back(scope);
    }

    // Collect all packages into our result object.
    for (auto package : compilation.getPackages()) {
        // Skip the built-in "std" package.
        if (package->name == "std")
            continue;

        auto scope = getAnalyzedScope(*package);
        SLANG_ASSERT(scope);
        result.packages.push_back(scope);
    }

    for (auto instance : root->topInstances)
        result.topInstances.emplace_back(analyzeSymbol(*instance));
    wait();

    // Report on unused definitions.
    if (hasFlag(AnalysisFlags::CheckUnused)) {
        auto& context = state().context;
        for (auto def : compilation.getUnreferencedDefinitions()) {
            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib(compilation, *def)) {
                context.addDiag(*def, diag::UnusedDefinition, def->location)
                    << def->getKindString();
            }
        }
    }

    return result;
}

const AnalyzedScope* AnalysisManager::getAnalyzedScope(const Scope& scope) {
    const AnalyzedScope* result = nullptr;
    analyzedScopes.cvisit(&scope, [&result](auto& item) {
        if (item.second)
            result = *item.second;
    });
    return result;
}

Diagnostics AnalysisManager::getDiagnostics(const SourceManager* sourceManager) {
    wait();

    ASTDiagMap diagMap;
    for (auto& state : workerStates) {
        for (auto& diag : state.context.diagnostics) {
            bool _;
            diagMap.add(diag, _);
        }
    }

    return diagMap.coalesce(sourceManager);
}

PendingAnalysis AnalysisManager::analyzeSymbol(const Symbol& symbol) {
    analyzeScopeAsync(getAsScope(symbol));
    return PendingAnalysis(*this, symbol);
}

void AnalysisManager::analyzeScopeAsync(const Scope& scope) {
    // Kick off a new analysis task if we haven't already seen
    // this scope before.
    if (analyzedScopes.try_emplace(&scope, std::nullopt)) {
        threadPool.detach_task([this, &scope] {
            SLANG_TRY {
                auto& result = analyzeScope(scope);
                analyzedScopes.visit(&scope, [&result](auto& item) { item.second = &result; });
            }
            SLANG_CATCH(...) {
                std::unique_lock lock(mutex);
                pendingException = std::current_exception();
            }
        });
    }
}

AnalysisManager::WorkerState& AnalysisManager::state() {
    return workerStates[BS::this_thread::get_index().value_or(workerStates.size() - 1)];
}

template<typename T, typename... U>
concept IsAnyOf = (std::same_as<T, U> || ...);

struct ScopeVisitor {
    AnalysisManager& manager;
    AnalysisContext& context;
    AnalyzedScope& result;

    ScopeVisitor(AnalysisManager& manager, AnalysisContext& context, AnalyzedScope& scope) :
        manager(manager), context(context), result(scope) {}

    void visit(const InstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const CheckerInstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const PackageSymbol& symbol) {
        // Kick off an async analysis of the package.
        // Our caller up the chain (we must be in a compilation unit here)
        // will take care of looking these up and hooking them into the
        // final AnalyzedDesign that we return.
        manager.analyzeScopeAsync(symbol);
    }

    void visit(const GenerateBlockSymbol& symbol) {
        if (symbol.isUninstantiated)
            return;

        // For our purposes we can just flatten the content of generate
        // blocks into their parents.
        visitMembers(symbol);
    }

    void visit(const GenerateBlockArraySymbol& symbol) {
        if (!symbol.valid)
            return;

        visitMembers(symbol);
    }

    void visit(const ProceduralBlockSymbol& symbol) {
        result.procedures.emplace_back(context, symbol);
    }

    void visit(const SubroutineSymbol& symbol) {
        if (symbol.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize |
                             MethodFlags::BuiltIn)) {
            return;
        }

        result.procedures.emplace_back(context, symbol);
        visitMembers(symbol);
    }

    void visit(const MethodPrototypeSymbol&) {
        // Deliberately don't visit the method prototype's formal arguments.
    }

    void visit(const ClassType& symbol) {
        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const CovergroupType& symbol) {
        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const GenericClassDefSymbol& symbol) {
        for (auto& spec : symbol.specializations())
            spec.visit(*this);
    }

    void visit(const NetSymbol& symbol) {
        if (symbol.isImplicit) {
            checkValueUnused(symbol, diag::UnusedImplicitNet, diag::UnusedImplicitNet,
                             diag::UnusedImplicitNet);
        }
        else {
            checkValueUnused(symbol, diag::UnusedNet, diag::UndrivenNet, diag::UnusedButSetNet);
        }
    }

    void visit(const VariableSymbol& symbol) {
        if (symbol.flags.has(VariableFlags::CompilerGenerated))
            return;

        if (symbol.kind == SymbolKind::Variable) {
            // Class handles and covergroups are considered used if they are
            // constructed, since construction can have side effects.
            auto& type = symbol.getType();
            if (type.isClass() || type.isCovergroup()) {
                if (auto init = symbol.getDeclaredType()->getInitializer();
                    init && (init->kind == ExpressionKind::NewClass ||
                             init->kind == ExpressionKind::NewCovergroup)) {
                    return;
                }
            }

            checkValueUnused(symbol, diag::UnusedVariable, diag::UnassignedVariable,
                             diag::UnusedButSetVariable);
        }
        else if (symbol.kind == SymbolKind::FormalArgument) {
            auto parent = symbol.getParentScope();
            SLANG_ASSERT(parent);

            if (parent->asSymbol().kind == SymbolKind::Subroutine) {
                auto& sub = parent->asSymbol().as<SubroutineSymbol>();
                if (!sub.isVirtual())
                    checkValueUnused(symbol, diag::UnusedArgument, std::nullopt, std::nullopt);
            }
        }
    }

    void visit(const ParameterSymbol& symbol) {
        checkValueUnused(symbol, diag::UnusedParameter, {}, diag::UnusedParameter);
    }

    void visit(const TypeParameterSymbol& symbol) {
        checkUnused(symbol, diag::UnusedTypeParameter);
    }

    void visit(const TypeAliasType& symbol) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        {
            auto [used, _] = isReferenced(*syntax);
            if (used)
                return;
        }

        // If this is a typedef for an enum declaration, count usage
        // of any of the enum values as a usage of the typedef itself
        // (since there's no good way otherwise to introduce enum values
        // without the typedef).
        auto& targetType = symbol.targetType.getType();
        if (targetType.kind == SymbolKind::EnumType) {
            for (auto& val : targetType.as<EnumType>().values()) {
                if (auto valSyntax = val.getSyntax()) {
                    auto [valUsed, _] = isReferenced(*valSyntax);
                    if (valUsed)
                        return;
                }
            }
        }

        addDiag(symbol, diag::UnusedTypedef);
    }

    void visit(const GenvarSymbol& symbol) { checkUnused(symbol, diag::UnusedGenvar); }

    void visit(const SequenceSymbol& symbol) { checkAssertionDeclUnused(symbol, "sequence"sv); }
    void visit(const PropertySymbol& symbol) { checkAssertionDeclUnused(symbol, "property"sv); }
    void visit(const LetDeclSymbol& symbol) { checkAssertionDeclUnused(symbol, "let"sv); }
    void visit(const CheckerSymbol& symbol) { checkAssertionDeclUnused(symbol, "checker"sv); }

    void visit(const ExplicitImportSymbol& symbol) { checkUnused(symbol, diag::UnusedImport); }

    void visit(const WildcardImportSymbol& symbol) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax)
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used) {
            if (shouldWarn(symbol))
                context.addDiag(symbol, diag::UnusedWildcardImport, symbol.location);
        }
    }

    template<typename T>
        requires(IsAnyOf<T, InstanceArraySymbol, ClockingBlockSymbol, AnonymousProgramSymbol,
                         SpecifyBlockSymbol, CovergroupBodySymbol, CoverCrossSymbol,
                         CoverCrossBodySymbol, StatementBlockSymbol, RandSeqProductionSymbol>)
    void visit(const T& symbol) {
        // For these symbol types we just descend into their members
        // and flatten them into their parent scope.
        visitMembers(symbol);
    }

    // Everything else doesn't need to be analyzed.
    template<typename T>
        requires(
            IsAnyOf<T, InvalidSymbol, RootSymbol, CompilationUnitSymbol, DefinitionSymbol,
                    AttributeSymbol, TransparentMemberSymbol, EmptyMemberSymbol, EnumValueSymbol,
                    ForwardingTypedefSymbol, PortSymbol, MultiPortSymbol, InterfacePortSymbol,
                    InstanceBodySymbol, ModportSymbol, ModportPortSymbol, ModportClockingSymbol,
                    ContinuousAssignSymbol, ElabSystemTaskSymbol, UninstantiatedDefSymbol,
                    ConstraintBlockSymbol, DefParamSymbol, SpecparamSymbol, PrimitiveSymbol,
                    PrimitivePortSymbol, PrimitiveInstanceSymbol, AssertionPortSymbol,
                    CoverpointSymbol, CoverageBinSymbol, TimingPathSymbol, PulseStyleSymbol,
                    SystemTimingCheckSymbol, NetAliasSymbol, ConfigBlockSymbol, NetType,
                    CheckerInstanceBodySymbol> ||
            std::is_base_of_v<Type, T>)
    void visit(const T&) {}

private:
    template<typename T>
    void visitMembers(const T& symbol) {
        for (auto& member : symbol.members())
            member.visit(*this);
    }

    void checkValueUnused(const ValueSymbol& symbol, DiagCode unusedCode,
                          std::optional<DiagCode> unsetCode, std::optional<DiagCode> unreadCode) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [rvalue, lvalue] = isReferenced(*syntax);

        auto portRef = symbol.getFirstPortBackref();
        if (portRef) {
            // This is a variable or net connected internally to a port.
            // If there is more than one port connection something unusually
            // complicated is going on so don't try to diagnose warnings.
            if (portRef->getNextBackreference())
                return;

            // Otherwise check and warn about the port being unused.
            switch (portRef->port->direction) {
                case ArgumentDirection::In:
                    if (!rvalue)
                        addDiag(symbol, diag::UnusedPort);
                    break;
                case ArgumentDirection::Out:
                    if (!lvalue)
                        addDiag(symbol, diag::UndrivenPort);
                    break;
                case ArgumentDirection::InOut:
                    if (!rvalue && !lvalue)
                        addDiag(symbol, diag::UnusedPort);
                    else if (!rvalue)
                        addDiag(symbol, diag::UnusedButSetPort);
                    else if (!lvalue)
                        addDiag(symbol, diag::UndrivenPort);
                    break;
                case ArgumentDirection::Ref:
                    if (!rvalue && !lvalue)
                        addDiag(symbol, diag::UnusedPort);
                    break;
            }
            return;
        }

        if (!rvalue && !lvalue)
            addDiag(symbol, unusedCode);
        else if (!rvalue && unreadCode)
            addDiag(symbol, *unreadCode);
        else if (!lvalue && !symbol.getDeclaredType()->getInitializerSyntax() && unsetCode)
            addDiag(symbol, *unsetCode);
    }

    void checkUnused(const Symbol& symbol, DiagCode code) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used)
            addDiag(symbol, code);
    }

    void checkAssertionDeclUnused(const Symbol& symbol, std::string_view kind) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used && shouldWarn(symbol)) {
            context.addDiag(symbol, diag::UnusedAssertionDecl, symbol.location)
                << kind << symbol.name;
        }
    }

    bool shouldWarn(const Symbol& symbol) {
        auto scope = symbol.getParentScope();
        return !scope->isUninstantiated() && scope->asSymbol().kind != SymbolKind::Package &&
               symbol.name != "_"sv && !hasUnusedAttrib(scope->getCompilation(), symbol);
    }

    void addDiag(const Symbol& symbol, DiagCode code) {
        if (shouldWarn(symbol))
            context.addDiag(symbol, code, symbol.location) << symbol.name;
    }

    std::pair<bool, bool> isReferenced(const syntax::SyntaxNode& node) const {
        return result.scope.getCompilation().isReferenced(node);
    }
};

const AnalyzedScope& AnalysisManager::analyzeScope(const Scope& scope) {
    auto& s = state();
    auto& result = *s.scopeAlloc.emplace(scope);

    ScopeVisitor visitor(*this, s.context, result);
    for (auto& member : scope.members())
        member.visit(visitor);

    return result;
}

void AnalysisManager::wait() {
    threadPool.wait();
    if (pendingException)
        std::rethrow_exception(pendingException);
}

} // namespace slang::analysis
