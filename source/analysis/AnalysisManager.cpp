//------------------------------------------------------------------------------
// AnalysisManager.cpp
// Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalysisManager.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"

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

const AnalyzedScope* PendingAnalysis::tryGet() const {
    return analysisManager->getAnalyzedScope(getAsScope(*symbol));
}

AnalysisManager::AnalysisManager(uint32_t numThreads) : threadPool(numThreads) {
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

Diagnostics AnalysisManager::getDiagnostics() {
    wait();

    Diagnostics diags;
    for (auto& state : workerStates)
        diags.append_range(state.context.diagnostics);

    return diags;
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
    AnalysisManager& analysisManager;
    AnalysisContext& context;
    AnalyzedScope& scope;

    ScopeVisitor(AnalysisManager& analysisManager, AnalysisContext& context, AnalyzedScope& scope) :
        analysisManager(analysisManager), context(context), scope(scope) {}

    void visit(const InstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        scope.childScopes.emplace_back(analysisManager.analyzeSymbol(symbol));
    }

    void visit(const CheckerInstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        scope.childScopes.emplace_back(analysisManager.analyzeSymbol(symbol));
    }

    void visit(const PackageSymbol& symbol) {
        // Kick off an async analysis of the package.
        // Our caller up the chain (we must be in a compilation unit here)
        // will take care of looking these up and hooking them into the
        // final AnalyzedDesign that we return.
        analysisManager.analyzeScopeAsync(symbol);
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
        scope.procedures.emplace_back(analysisManager, context, symbol);
    }

    void visit(const SubroutineSymbol& symbol) {
        if (symbol.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize)) {
            return;
        }

        scope.procedures.emplace_back(analysisManager, context, symbol);
    }

    void visit(const MethodPrototypeSymbol&) {
        // Deliberately don't visit the method prototype's formal arguments.
    }

    void visit(const ClassType& symbol) {
        scope.childScopes.emplace_back(analysisManager.analyzeSymbol(symbol));
    }

    void visit(const CovergroupType& symbol) {
        scope.childScopes.emplace_back(analysisManager.analyzeSymbol(symbol));
    }

    void visit(const GenericClassDefSymbol& symbol) {
        for (auto& spec : symbol.specializations())
            spec.visit(*this);
    }

    template<typename T>
        requires(IsAnyOf<T, InstanceArraySymbol, ClockingBlockSymbol, AnonymousProgramSymbol,
                         SpecifyBlockSymbol, CovergroupBodySymbol, CoverCrossSymbol,
                         CoverCrossBodySymbol>)
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
                    ForwardingTypedefSymbol, ParameterSymbol, TypeParameterSymbol, PortSymbol,
                    MultiPortSymbol, InterfacePortSymbol, InstanceBodySymbol, ExplicitImportSymbol,
                    WildcardImportSymbol, StatementBlockSymbol, NetSymbol, VariableSymbol,
                    FormalArgumentSymbol, FieldSymbol, ClassPropertySymbol, ModportSymbol,
                    ModportPortSymbol, ModportClockingSymbol, ContinuousAssignSymbol, GenvarSymbol,
                    ElabSystemTaskSymbol, UninstantiatedDefSymbol, IteratorSymbol, PatternVarSymbol,
                    ConstraintBlockSymbol, DefParamSymbol, SpecparamSymbol, PrimitiveSymbol,
                    PrimitivePortSymbol, PrimitiveInstanceSymbol, SequenceSymbol, PropertySymbol,
                    AssertionPortSymbol, ClockVarSymbol, LocalAssertionVarSymbol, LetDeclSymbol,
                    CheckerSymbol, RandSeqProductionSymbol, CoverpointSymbol, CoverageBinSymbol,
                    TimingPathSymbol, PulseStyleSymbol, SystemTimingCheckSymbol, NetAliasSymbol,
                    ConfigBlockSymbol, TypeAliasType, NetType, CheckerInstanceBodySymbol> ||
            std::is_base_of_v<Type, T>)
    void visit(const T&) {}

    template<typename T>
    void visitMembers(const T& symbol) {
        for (auto& member : symbol.members())
            member.visit(*this);
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
