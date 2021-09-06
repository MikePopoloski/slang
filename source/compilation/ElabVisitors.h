//------------------------------------------------------------------------------
// ElabVisitors.h
// Internal visitors of the AST to support elaboration
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/util/StackContainer.h"

namespace slang {

// This visitor is used to touch every node in the AST to ensure that all lazily
// evaluated members have been realized and we have recorded every diagnostic.
struct DiagnosticVisitor : public ASTVisitor<DiagnosticVisitor, false, false> {
    DiagnosticVisitor(Compilation& compilation, const size_t& numErrors, uint32_t errorLimit) :
        compilation(compilation), numErrors(numErrors), errorLimit(errorLimit) {}

    template<typename T>
    void handle(const T& symbol) {
        handleDefault(symbol);
    }

    template<typename T>
    bool handleDefault(const T& symbol) {
        if (numErrors > errorLimit || hierarchyProblem)
            return false;

        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto declaredType = symbol.getDeclaredType();
            if (declaredType) {
                declaredType->getType();
                declaredType->getInitializer();
            }

            if constexpr (std::is_same_v<ParameterSymbol, T> ||
                          std::is_same_v<EnumValueSymbol, T> ||
                          std::is_same_v<SpecparamSymbol, T>) {
                symbol.getValue();
            }

            for (auto attr : compilation.getAttributes(symbol))
                attr->getValue();
        }

        if constexpr (is_detected_v<getBody_t, T>) {
            auto& body = symbol.getBody();
            if (body.bad())
                return true;

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

    void handle(const ContinuousAssignSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getAssignment();
        symbol.getDelay();
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
    }

    void handle(const GenericClassDefSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        // Save this for later; we need to revist all generic classes
        // once we've finished checking everything else.
        genericClasses.append(&symbol);
    }

    void handle(const NetType& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDataType();
    }

    void handle(const NetSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDelay();
        symbol.checkInitializer();
    }

    void handle(const ConstraintBlockSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getConstraints();
    }

    void handle(const UnknownModuleSymbol& symbol) {
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

    void handle(const ClockingBlockSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getEvent();
        symbol.getDefaultInputSkew();
        symbol.getDefaultOutputSkew();
    }

    void handle(const InstanceSymbol& symbol) {
        if (numErrors > errorLimit || hierarchyProblem)
            return;

        instanceCount[&symbol.getDefinition()]++;
        symbol.resolvePortConnections();
        for (auto attr : compilation.getAttributes(symbol))
            attr->getValue();

        // Detect infinite recursion, which happens if we see this exact
        // instance body somewhere higher up in the stack.
        if (!activeInstanceBodies.emplace(&symbol.body).second) {
            symbol.getParentScope()->addDiag(diag::InfinitelyRecursiveHierarchy, symbol.location)
                << symbol.name;
            hierarchyProblem = true;
            return;
        }

        auto guard = ScopeGuard([this, &symbol] { activeInstanceBodies.erase(&symbol.body); });

        // Instance bodies are all the same, so if we've visited this one
        // already don't bother doing it again.
        if (!visitedInstanceBodies.emplace(&symbol.body).second)
            return;

        // In order to avoid "effectively infinite" recursions, where parameter values
        // are changing but the numbers are so huge that we would run for almost forever,
        // check the depth and bail out after a certain configurable point.
        if (activeInstanceBodies.size() > compilation.getOptions().maxInstanceDepth) {
            auto& diag =
                symbol.getParentScope()->addDiag(diag::MaxInstanceDepthExceeded, symbol.location);
            diag << symbol.getDefinition().getKindString();
            diag << compilation.getOptions().maxInstanceDepth;
            hierarchyProblem = true;
            return;
        }

        visit(symbol.body);
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (!symbol.isInstantiated)
            return;
        handleDefault(symbol);
    }

    void handle(const SubroutineSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        if (symbol.flags.has(MethodFlags::DPIImport))
            dpiImports.append(&symbol);
    }

    void handle(const DefParamSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getTarget();
        symbol.getValue();
    }

    void handle(const SequenceSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const PropertySymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const LetDeclSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.makeDefaultInstance();
    }

    void handle(const RandSeqProductionSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getRules();
    }

    void finalize() {
        // Once everything has been visited, go back over and check things that might
        // have been influenced by visiting later symbols. Unfortunately visiting
        // a specialization can trigger more specializations to be made for the
        // same or other generic classs, so we need to be careful here when iterating.
        SmallSet<const Type*, 8> visitedSpecs;
        SmallVectorSized<const Type*, 8> toVisit;
        bool didSomething;
        do {
            didSomething = false;
            for (auto symbol : genericClasses) {
                for (auto& spec : symbol->specializations()) {
                    if (visitedSpecs.emplace(&spec).second)
                        toVisit.append(&spec);
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
    }

    Compilation& compilation;
    const size_t& numErrors;
    flat_hash_map<const Definition*, size_t> instanceCount;
    flat_hash_set<const InstanceBodySymbol*> visitedInstanceBodies;
    flat_hash_set<const InstanceBodySymbol*> activeInstanceBodies;
    uint32_t errorLimit;
    SmallVectorSized<const GenericClassDefSymbol*, 8> genericClasses;
    SmallVectorSized<const SubroutineSymbol*, 4> dpiImports;
    bool hierarchyProblem = false;
};

// This visitor is for finding all bind directives in the hierarchy.
struct BindVisitor : public ASTVisitor<BindVisitor, false, false> {
    BindVisitor(const flat_hash_set<const BindDirectiveSyntax*>& foundDirectives, size_t expected) :
        foundDirectives(foundDirectives), expected(expected) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }

    void handle(const CompilationUnitSymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;
        visitDefault(symbol);
    }

    void handle(const InstanceSymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;

        if (!visitedInstances.emplace(&symbol.body).second) {
            errored = true;
            return;
        }

        visitDefault(symbol.body);
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (foundDirectives.size() == expected || !symbol.isInstantiated)
            return;
        visitDefault(symbol);
    }

    void handle(const GenerateBlockArraySymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;

        auto members = symbol.members();
        if (members.begin() == members.end())
            return;

        visit(*members.begin());
    }

    template<typename T>
    void handle(const T&) {}

    const flat_hash_set<const BindDirectiveSyntax*>& foundDirectives;
    flat_hash_set<const InstanceBodySymbol*> visitedInstances;
    size_t expected;
    bool errored = false;
};

// This visitor is for finding all defparam directives in the hierarchy.
struct DefParamVisitor : public ASTVisitor<DefParamVisitor, false, false> {
    DefParamVisitor(size_t maxInstanceDepth, size_t generateLevel) :
        maxInstanceDepth(maxInstanceDepth), generateLevel(generateLevel) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }
    void handle(const CompilationUnitSymbol& symbol) { visitDefault(symbol); }
    void handle(const DefParamSymbol& symbol) { found.append(&symbol); }

    void handle(const InstanceSymbol& symbol) {
        if (hierarchyProblem)
            return;

        if (instanceDepth > maxInstanceDepth) {
            hierarchyProblem = &symbol;
            return;
        }

        numBlocksSeen++;
        instanceDepth++;
        visitDefault(symbol.body);
        instanceDepth--;
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (!symbol.isInstantiated || generateDepth >= generateLevel || hierarchyProblem)
            return;

        numBlocksSeen++;
        generateDepth++;
        visitDefault(symbol);
        generateDepth--;
    }

    void handle(const GenerateBlockArraySymbol& symbol) {
        for (auto& member : symbol.members())
            visit(member);
    }

    template<typename T>
    void handle(const T&) {}

    SmallVectorSized<const DefParamSymbol*, 8> found;
    size_t instanceDepth = 0;
    size_t maxInstanceDepth = 0;
    size_t generateLevel = 0;
    size_t numBlocksSeen = 0;
    size_t generateDepth = 0;
    const InstanceSymbol* hierarchyProblem = nullptr;
};

} // namespace slang
