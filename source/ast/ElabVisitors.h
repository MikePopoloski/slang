//------------------------------------------------------------------------------
// ElabVisitors.h
// Internal visitors of the AST to support elaboration
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/util/TimeTrace.h"

namespace slang::ast {

using namespace syntax;

// This visitor is used to touch every node in the AST to ensure that all lazily
// evaluated members have been realized and we have recorded every diagnostic.
struct DiagnosticVisitor : public ASTVisitor<DiagnosticVisitor, false, false> {
    DiagnosticVisitor(Compilation& compilation, const size_t& numErrors, uint32_t errorLimit) :
        compilation(compilation), numErrors(numErrors), errorLimit(errorLimit) {}

    bool finishedEarly() const { return numErrors > errorLimit || hierarchyProblem; }

    template<typename T>
    void handle(const T& symbol) {
        handleDefault(symbol);
    }

    template<typename T>
    bool handleDefault(const T& symbol) {
        if (finishedEarly())
            return false;

        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto declaredType = symbol.getDeclaredType();
            if (declaredType) {
                declaredType->getType();
                declaredType->getInitializer();
            }

            if constexpr (std::is_same_v<EnumValueSymbol, T> ||
                          std::is_same_v<SpecparamSymbol, T>) {
                symbol.getValue();
            }
        }

        if constexpr (requires { symbol.getBody().bad(); }) {
            auto& body = symbol.getBody();
            if (!body.bad())
                body.visit(*this);
        }

        visitDefault(symbol);
        return true;
    }

    void handle(const ExplicitImportSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.importedSymbol();
    }

    void handle(const WildcardImportSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getPackage();
    }

    void handle(const PackageSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.checkExplicitExports();
    }

    void handle(const InterfacePortSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getDeclaredRange();

        if (symbol.interfaceDef) {
            usedIfacePorts.emplace(symbol.interfaceDef);

            // If this interface port specifies a modport and that
            // modport has export methods, store it in a list for later
            // processing and checking.
            if (!symbol.modport.empty()) {
                auto [_, modport] = symbol.getConnection();
                if (modport) {
                    for (auto& method : modport->membersOfType<MethodPrototypeSymbol>()) {
                        if (method.flags.has(MethodFlags::ModportExport)) {
                            modportsWithExports.push_back({&symbol, modport});
                            break;
                        }
                    }
                }
            }
        }
    }

    void handle(const PortSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getType();
        symbol.getInitializer();
    }

    void handle(const MultiPortSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getType();
    }

    void handle(const ParameterSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getValue();
        if (symbol.isOverridden())
            symbol.checkDefaultExpression();
    }

    void handle(const TypeParameterSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.checkTypeRestriction();
        if (symbol.isOverridden())
            symbol.checkDefaultExpression();
    }

    void handle(const ContinuousAssignSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getAssignment();
        symbol.getDelay();
    }

    void handle(const NetAliasSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getNetReferences();
    }

    void handle(const ElabSystemTaskSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.issueDiagnostic();
    }

    void handle(const MethodPrototypeSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        if (auto sub = symbol.getSubroutine())
            handle(*sub);

        if (symbol.flags.has(MethodFlags::InterfaceExtern)) {
            externIfaceProtos.push_back(&symbol);

            auto scope = symbol.getParentScope();
            SLANG_ASSERT(scope);
            compilation.noteCannotCache(*scope);
        }
    }

    void handle(const GenericClassDefSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        // Save this for later; we need to revist all generic classes
        // once we've finished checking everything else.
        genericClasses.push_back(&symbol);
    }

    void handle(const NetType& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDataType();
        symbol.getResolutionFunction();
    }

    void handle(const ClassType& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getBaseConstructorCall();
        symbol.getBitstreamWidth();
    }

    void handle(const CovergroupType& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getCoverageEvent();
        for (auto& option : symbol.getBody().options)
            option.getExpression();
    }

    void handle(const CoverpointSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getIffExpr();
        symbol.checkBins();
        for (auto& option : symbol.options)
            option.getExpression();
    }

    void handle(const CoverCrossSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getIffExpr();
        for (auto& option : symbol.options)
            option.getExpression();
    }

    void handle(const CoverageBinSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getValues();
    }

    void handle(const NetSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDelay();
        symbol.checkInitializer();
    }

    void handle(const VariableSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.checkInitializer();
    }

    void handle(const FormalArgumentSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getDefaultValue();
    }

    void handle(const ConstraintBlockSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getConstraints();
    }

    void handle(const UninstantiatedDefSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getPortConnections();
    }

    void handle(const PrimitiveInstanceSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getPortConnections();
        symbol.getDelay();
    }

    void handle(const CheckerInstanceSymbol& symbol) {
        if (finishedEarly())
            return;

        visit(symbol.body);

        if (!finishedEarly()) {
            for (auto& conn : symbol.getPortConnections())
                conn.getOutputInitialExpr();

            symbol.verifyMembers();
        }
    }

    void handle(const CheckerInstanceBodySymbol& symbol) {
        if (!visitInstances || finishedEarly())
            return;

        if (symbol.instanceDepth > compilation.getOptions().maxCheckerInstanceDepth) {
            hierarchyProblem = true;
            return;
        }

        visitDefault(symbol);
    }

    void handle(const ClockingBlockSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getEvent();
        symbol.getDefaultInputSkew();
        symbol.getDefaultOutputSkew();
    }

    void handle(const InstanceSymbol& symbol) {
        if (finishedEarly())
            return;

        // If we're not visiting instances and this instance came from a bind directive
        // we don't even want to look at its port connections right now. This is because
        // we are probably doing a force elaborate due to a wildcard package import and
        // bind directive connections don't contribute to the set of imported symbols
        // from wildcard imports, and if we visit connections anyway we can get into a
        // recursive loop when trying to resolve bind port connections. We will come back
        // and visit this instance later during the normal elaboration process.
        if (!visitInstances && symbol.body.flags.has(InstanceFlags::FromBind))
            return;

        TimeTraceScope timeScope("AST Instance", [&] { return symbol.getHierarchicalPath(); });

        for (auto conn : symbol.getPortConnections())
            conn->getExpression();

        if (!visitInstances)
            return;

        // In order to avoid "effectively infinite" recursions, where parameter values
        // are changing but the numbers are so huge that we would run for almost forever,
        // check the depth and bail out after a certain configurable point.
        auto guard = ScopeGuard([this, &symbol] { activeInstanceBodies.erase(&symbol.body); });
        activeInstanceBodies.emplace(&symbol.body);
        if (activeInstanceBodies.size() > compilation.getOptions().maxInstanceDepth) {
            auto& diag = symbol.getParentScope()->addDiag(diag::MaxInstanceDepthExceeded,
                                                          symbol.location);
            diag << symbol.getDefinition().getKindString();
            diag << compilation.getOptions().maxInstanceDepth;
            hierarchyProblem = true;
            return;
        }

        // If we have already visited an identical instance body we don't have to do
        // it again, because all possible diagnostics have already been collected.
        // Otherwise descend into the body and visit everything.
        if (!tryApplyFromCache(symbol)) {
            visit(symbol.body);
        }
        else if (activeInstanceBodies.contains(symbol.getCanonicalBody())) {
            // Detect infinite recursion that we missed earlier because of caching.
            auto name = symbol.name.empty() ? "<unnamed instance>"sv : symbol.name;
            symbol.getParentScope()->addDiag(diag::InfinitelyRecursiveHierarchy, symbol.location)
                << name;
            hierarchyProblem = true;
        }
    }

    void handle(const SubroutineSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        if (symbol.flags.has(MethodFlags::DPIImport))
            dpiImports.push_back(&symbol);
    }

    void handle(const DefParamSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getTarget();
        symbol.getValue();
    }

    void handle(const SequenceSymbol& symbol) {
        if (!visitInstances || !handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const PropertySymbol& symbol) {
        if (!visitInstances || !handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const LetDeclSymbol& symbol) {
        if (!visitInstances || !handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const CheckerSymbol& symbol) {
        if (!visitInstances || !handleDefault(symbol))
            return;

        auto& result = CheckerInstanceSymbol::createInvalid(symbol, 0);
        result.visit(*this);
    }

    void handle(const RandSeqProductionSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getRules();
    }

    void handle(const TimingPathSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.checkDuplicatePaths(timingPathMap);
    }

    void handle(const PulseStyleSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.checkPreviouslyUsed(timingPathMap);
    }

    void handle(const SystemTimingCheckSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getArguments();
    }

    void handle(const SpecparamSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getPathSource();
    }

    void finalize() {
        // Once everything has been visited, go back over and check things that might
        // have been influenced by visiting later symbols.

        // For all hierarchical assignments, make sure we actually visited their
        // target instances and didn't skip them due to caching.
        while (!compilation.hierarchicalAssignments.empty()) {
            disableCache = true;
            auto hierarchicalAssignments = std::move(compilation.hierarchicalAssignments);
            compilation.hierarchicalAssignments.clear();

            for (auto hierRef : hierarchicalAssignments) {
                // Walk the path and visit all instances we find that were previously cached.
                for (auto& [sym, _] : hierRef->path) {
                    if (sym->kind == SymbolKind::Instance) {
                        // If this instance has a canonical pointer it means we previously
                        // determined we could cache it, so we need to visit it here.
                        // Additionally we will unset the canonical pointer so that
                        // we don't try to cache it again in the future.
                        auto& inst = sym->as<InstanceSymbol>();
                        if (inst.getCanonicalBody() != nullptr) {
                            inst.setCanonicalBody(nullptr);
                            inst.visit(*this);
                        }
                    }
                }
            }
        }

        // Check the validity of virtual interface assignments.
        while (!compilation.virtualIfaceInstances.empty()) {
            auto vii = std::move(compilation.virtualIfaceInstances);
            compilation.virtualIfaceInstances.clear();

            for (auto inst : vii) {
                inst->visit(*this);
                compilation.checkVirtualIfaceInstance(*inst);
            }
        }

        // Visiting a specialization can trigger more specializations to be made for the
        // same or other generic classes, so we need to be careful here when iterating.
        SmallSet<const Type*, 8> visitedSpecs;
        SmallVector<const Type*> toVisit;
        bool didSomething;
        do {
            didSomething = false;
            for (auto symbol : genericClasses) {
                for (auto& spec : symbol->specializations()) {
                    if (visitedSpecs.emplace(&spec).second)
                        toVisit.push_back(&spec);
                }

                for (auto spec : toVisit) {
                    spec->visit(*this);
                    didSomething = true;
                }

                toVisit.clear();
            }
        } while (didSomething);

        // Go back over and find generic classes that were never instantiated
        // and force an empty one to make sure we collect all diagnostics that
        // don't depend on parameter values.
        for (auto symbol : genericClasses) {
            if (symbol->numSpecializations() == 0)
                symbol->getInvalidSpecialization().visit(*this);
        }

        // Visit all attributes and force their values to resolve.
        for (auto& [_, attrList] : compilation.attributeMap) {
            for (auto attr : attrList)
                attr->getValue();
        }
    }

    static bool isWithinInterface(const InstanceSymbol& symbol) {
        auto scope = symbol.getParentScope();
        while (scope) {
            auto container = scope->getContainingInstance();
            if (!container || !container->parentInstance)
                return false;

            if (container->parentInstance->isInterface())
                return true;

            scope = container->parentInstance->getParentScope();
        }
        return false;
    }

    bool tryApplyFromCache(const InstanceSymbol& symbol) {
        if (disableCache)
            return false;

        // We can use a cached version of this instance's body if we have already
        // visited an identical body elsewhere, with some caveats explained below.
        SLANG_ASSERT(symbol.getCanonicalBody() == nullptr);

        // Instances that are targeted by defparams, bind directives, or configuration rules,
        // or that are themselves created by a bind directive, cannot participate in caching.
        if (!InstanceCacheKey::isEligibleForCaching(symbol))
            return false;

        // "Identical" needs to take into account parameter values and interface ports,
        // since the types of members and expression can vary based on those. This is
        // computed in the InstanceCacheKey.
        //
        // Interface ports must be connected to instances that themselves follow the
        // restrictions on defparams, bind directives, and config rules. This is checked
        // in the InstanceCacheKey constructor and returned in the 'valid' parameter.
        bool valid = true;
        SmallSet<const InstanceSymbol*, 2> visitedInstances;
        InstanceCacheKey key(symbol, valid, visitedInstances);
        if (!valid)
            return false;

        auto [it, inserted] = instanceCache.try_emplace(std::move(key), symbol.body);
        if (inserted)
            return false;

        // If we haven't resolved the side effects entry yet do that now.
        // We do this opportunistically here because we know we have a cache hit.
        auto& entry = it->second;
        if (!entry.sideEffects) {
            if (auto sideEffectIt = compilation.instanceSideEffectMap.find(entry.canonicalBody);
                sideEffectIt != compilation.instanceSideEffectMap.end()) {
                entry.sideEffects = sideEffectIt->second.get();
            }
            else {
                entry.sideEffects = nullptr;
            }
        }

        // If any hierarchical names extend upward out of the instance we won't consider
        // it for caching, since the names could be different based on the context.
        // This could be optimized in the future by having another layer of caching based
        // on what the name resolves to for each instance.
        auto sideEffects = entry.sideEffects.value();
        if (sideEffects && (sideEffects->cannotCache || !sideEffects->upwardNames.empty())) {
            return false;
        }

        // Assuming we find an appropriately cached instance, we will store a pointer to it
        // in other instances to facilitate downstream consumers in not needing to recreate
        // this duplication detection logic again.
        symbol.setCanonicalBody(entry.canonicalBody);

        // If this is an interface or an instance instantiated within an interface
        // we want to return false so that we continue visiting the body. This is
        // because we're very likely going to be connected to a module port and need
        // all types resolved before we freeze the compilation and move on to the
        // multithreaded analysis phase.
        auto defKind = symbol.getDefinition().definitionKind;
        if (compilation.hasFlag(CompilationFlags::DisableInstanceCaching) ||
            defKind == DefinitionKind::Interface ||
            (defKind == DefinitionKind::Program && isWithinInterface(symbol))) {
            return false;
        }

        return true;
    }

    struct InstanceCacheEntry {
        not_null<const InstanceBodySymbol*> canonicalBody;
        std::optional<const Compilation::InstanceSideEffects*> sideEffects;

        explicit InstanceCacheEntry(const InstanceBodySymbol& canonicalBody) :
            canonicalBody(&canonicalBody) {}
    };

    Compilation& compilation;
    const size_t& numErrors;
    uint32_t errorLimit;
    bool visitInstances = true;
    bool disableCache = false;
    bool hierarchyProblem = false;
    flat_hash_map<InstanceCacheKey, InstanceCacheEntry> instanceCache;
    flat_hash_set<const InstanceBodySymbol*> activeInstanceBodies;
    flat_hash_set<const DefinitionSymbol*> usedIfacePorts;
    SmallVector<const GenericClassDefSymbol*> genericClasses;
    SmallVector<const SubroutineSymbol*> dpiImports;
    SmallVector<const MethodPrototypeSymbol*> externIfaceProtos;
    SmallVector<std::pair<const InterfacePortSymbol*, const ModportSymbol*>> modportsWithExports;
    TimingPathMap timingPathMap;
};

// This visitor is for finding all defparam directives in the hierarchy.
// We're given a target generate "level" to reach, where the level is a measure
// of how deep the design is in terms of nested generate blocks. Once we reach
// the target level we don't go any deeper, except for the following case:
//
// If we find a potentially infinitely recursive module (because it instantiates
// itself directly or indirectly) we will continue traversing deeper to see if we
// hit the limit for max depth, which lets us bail out of defparam evaluation completely.
// Since defparams are disallowed from modifying parameters above them across generate
// blocks, an infinitely recursive module instantiation can't be stopped by a deeper
// defparam evaluation.
//
// This visitor also implicitly serves to discover bind directives. They are registered
// with the compilation by Scope::addMembers and then get processed after we finish
// visiting the tree.
struct DefParamVisitor : public ASTVisitor<DefParamVisitor, false, false> {
    DefParamVisitor(size_t maxInstanceDepth, size_t maxBlocks, size_t generateLevel) :
        maxInstanceDepth(maxInstanceDepth), generateLevel(generateLevel), maxBlocks(maxBlocks) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }
    void handle(const CompilationUnitSymbol& symbol) { visitDefault(symbol); }

    void handle(const DefParamSymbol& symbol) {
        if (generateDepth <= generateLevel)
            found.push_back(&symbol);
        else
            skippedAnything = true;
    }

    void handle(const InstanceSymbol& symbol) {
        if (symbol.name.empty() || symbol.body.flags.has(InstanceFlags::Uninstantiated) ||
            hierarchyProblem) {
            return;
        }

        // If we hit max depth we have a problem -- setting the hierarchyProblem
        // member will cause other functions to early out so that we complete
        // this visitation as quickly as possible.
        if (instanceDepth > maxInstanceDepth || numBlocksSeen > maxBlocks) {
            hierarchyProblem = &symbol;
            return;
        }

        bool inserted = false;
        const bool wasInRecursive = inRecursiveInstance;
        if (!inRecursiveInstance) {
            // If the instance's definition is already in the active set,
            // we potentially have an infinitely recursive instantiation and
            // need to go all the way to the maximum depth to find out.
            inserted = activeInstances.emplace(&symbol.getDefinition()).second;
            if (!inserted)
                inRecursiveInstance = true;
        }

        // If we're past our target depth because we're searching for a potentially
        // infinitely recursive instantiation, don't count the block.
        if (generateDepth <= generateLevel)
            numBlocksSeen++;

        instanceDepth++;
        visitDefault(symbol.body);
        instanceDepth--;

        inRecursiveInstance = wasInRecursive;
        if (inserted)
            activeInstances.erase(&symbol.getDefinition());
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (symbol.isUninstantiated || hierarchyProblem)
            return;

        if (generateDepth >= generateLevel) {
            skippedAnything = true;
            if (!inRecursiveInstance)
                return;
        }

        // We don't count the case where we are *at* the target level
        // because we're about to descend into the generate block,
        // so it counts as deeper level.
        if (generateDepth < generateLevel)
            numBlocksSeen++;

        generateDepth++;
        visitDefault(symbol);
        generateDepth--;
    }

    void handle(const GenerateBlockArraySymbol& symbol) {
        for (auto& member : symbol.members()) {
            if (hierarchyProblem)
                return;
            member.visit(*this);
        }
    }

    template<typename T>
    void handle(const T&) {}

    SmallVector<const DefParamSymbol*> found;
    flat_hash_set<const DefinitionSymbol*> activeInstances;
    size_t instanceDepth = 0;
    size_t maxInstanceDepth = 0;
    size_t generateLevel = 0;
    size_t numBlocksSeen = 0;
    size_t maxBlocks = 0;
    size_t generateDepth = 0;
    bool inRecursiveInstance = false;
    bool skippedAnything = false;
    const InstanceSymbol* hierarchyProblem = nullptr;
};

} // namespace slang::ast
