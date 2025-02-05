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

const AnalyzedScope* AnalyzedInstance::getBody() const {
    return analysisManager.getAnalyzedScope(symbol.body);
}

AnalysisManager::AnalysisManager(uint32_t numThreads) : threadPool(numThreads) {
    workerStates.resize(threadPool.get_thread_count() + 1);
}

AnalyzedDesign AnalysisManager::analyze(const Compilation& compilation) {
    SLANG_ASSERT(compilation.isFinalized());
    SLANG_ASSERT(compilation.isFrozen());

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
        result.topInstances.emplace_back(analyzeInst(*instance));
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

AnalyzedInstance AnalysisManager::analyzeInst(const InstanceSymbol& instance) {
    // If there is a canonical body set, use that. Otherwise use the
    // instance's body directly.
    auto body = instance.getCanonicalBody();
    if (!body)
        body = &instance.body;

    analyzeScopeAsync(*body);

    return AnalyzedInstance(*this, instance);
}

void AnalysisManager::analyzeScopeAsync(const Scope& scope) {
    // Kick off a new analysis task if we haven't already seen
    // this scope before.
    if (analyzedScopes.try_emplace(&scope, std::nullopt)) {
        threadPool.detach_task([this, &scope] {
            try {
                auto& result = analyzeScope(scope);
                analyzedScopes.visit(&scope, [&result](auto& item) { item.second = &result; });
            }
            catch (...) {
                std::unique_lock lock(mutex);
                pendingException = std::current_exception();
            }
        });
    }
}

AnalysisManager::WorkerState& AnalysisManager::state() {
    return workerStates[BS::this_thread::get_index().value_or(workerStates.size() - 1)];
}

struct ScopeVisitor {
    AnalysisManager& analysisManager;
    AnalyzedScope& scope;

    ScopeVisitor(AnalysisManager& analysisManager, AnalyzedScope& scope) :
        analysisManager(analysisManager), scope(scope) {}

    void visit(const InstanceSymbol& symbol) {
        scope.instances.emplace_back(analysisManager.analyzeInst(symbol));
    }

    void visit(const PackageSymbol& symbol) {
        // Kick off an async analysis of the package.
        // Our caller up the chain (we must be in a compilation unit here)
        // will take care of looking these up and hooking them into the
        // final AnalyzedDesign that we return.
        analysisManager.analyzeScopeAsync(symbol);
    }

    void visit(const GenerateBlockSymbol& symbol) {
        // For our purposes we can just flatten the content of generate
        // blocks into their parents.
        for (auto& member : symbol.members())
            member.visit(*this);
    }

    void visit(const GenerateBlockArraySymbol& symbol) {
        for (auto& member : symbol.members())
            member.visit(*this);
    }

    void visit(const ProceduralBlockSymbol& symbol) {
        scope.procedures.emplace_back(analysisManager, symbol);
    }

    // Everything else is unhandled.
    // TODO: make sure we handle all relevant cases
    template<typename T>
    void visit(const T&) {}
};

const AnalyzedScope& AnalysisManager::analyzeScope(const Scope& scope) {
    auto& result = *state().scopeAlloc.emplace(scope);

    ScopeVisitor visitor(*this, result);
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
