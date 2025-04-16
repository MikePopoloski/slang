//------------------------------------------------------------------------------
// ElabVisitors.h
// Internal visitors of the AST to support elaboration
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/util/TimeTrace.h"

namespace slang::ast {

class InstanceCacheKey {
public:
    InstanceCacheKey(const InstanceSymbol& symbol);

    bool operator==(const InstanceCacheKey& other) const;
    bool operator!=(const InstanceCacheKey& other) const { return !(*this == other); }

    size_t hash() const { return savedHash; }

private:
    not_null<const InstanceSymbol*> symbol;
    std::vector<InstanceCacheKey> ifaceKeys;
    size_t savedHash;
};

} // namespace slang::ast

namespace slang {

template<>
struct hash<ast::InstanceCacheKey> {
    size_t operator()(const ast::InstanceCacheKey& key) const noexcept { return key.hash(); }
};

} // namespace slang

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
                if (modport)
                    modportsWithExports.push_back({&symbol, modport});
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

        if (symbol.flags.has(MethodFlags::InterfaceExtern))
            externIfaceProtos.push_back(&symbol);
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

        TimeTraceScope timeScope("AST Instance", [&] {
            std::string buffer;
            symbol.getHierarchicalPath(buffer);
            return buffer;
        });

        for (auto conn : symbol.getPortConnections()) {
            conn->getExpression();
            conn->checkSimulatedNetTypes();
        }

        // Detect infinite recursion, which happens if we see this exact
        // instance body somewhere higher up in the stack.
        if (!activeInstanceBodies.emplace(&symbol.body).second) {
            symbol.getParentScope()->addDiag(diag::InfinitelyRecursiveHierarchy, symbol.location)
                << symbol.name;
            hierarchyProblem = true;
            return;
        }

        // In order to avoid "effectively infinite" recursions, where parameter values
        // are changing but the numbers are so huge that we would run for almost forever,
        // check the depth and bail out after a certain configurable point.
        auto guard = ScopeGuard([this, &symbol] { activeInstanceBodies.erase(&symbol.body); });
        if (activeInstanceBodies.size() > compilation.getOptions().maxInstanceDepth) {
            auto& diag = symbol.getParentScope()->addDiag(diag::MaxInstanceDepthExceeded,
                                                          symbol.location);
            diag << symbol.getDefinition().getKindString();
            diag << compilation.getOptions().maxInstanceDepth;
            hierarchyProblem = true;
            return;
        }

        // If we have already visited an identical instance body we don't have to do
        // it again, because all possible diagnostics have already been collected,
        // with some notable caveats that need to be handled:
        // - "identical" needs to take into account parameters values and interface ports,
        //   since they types of members and expression can vary based on those
        // - TODO: Any upward hierarchical references that extend out of the instance need
        //         to be re-resolved here, and the resolved types must match
        // - TODO: Downward hierarchical references into such instances need to be accounted for
        // - TODO: Bind directives needs to be accounted for
        // - TODO: Defparams need to be accounted for
        // - TODO: Configuration rules need to be accounted for
        //
        // Assuming we find an appropriately cached instance, we will store a pointer to it
        // in other instances to facilitate downstream consumers in not needing to recreate
        // this duplication detection logic again.
        SLANG_ASSERT(symbol.getCanonicalBody() == nullptr);
        auto [it, inserted] = instanceCache.try_emplace(symbol, &symbol.body);
        if (!inserted) {
            symbol.setCanonicalBody(*it->second);
            if (!compilation.hasFlag(CompilationFlags::DisableInstanceCaching))
                return;
        }

        if (visitInstances)
            visit(symbol.body);
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
        while (!compilation.virtualInterfaceInstances.empty()) {
            auto vii = compilation.virtualInterfaceInstances;
            compilation.virtualInterfaceInstances.clear();

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

    Compilation& compilation;
    const size_t& numErrors;
    uint32_t errorLimit;
    bool visitInstances = true;
    bool hierarchyProblem = false;
    flat_hash_map<InstanceCacheKey, const InstanceBodySymbol*> instanceCache;
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
    DefParamVisitor(size_t maxInstanceDepth, size_t generateLevel) :
        maxInstanceDepth(maxInstanceDepth), generateLevel(generateLevel) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }
    void handle(const CompilationUnitSymbol& symbol) { visitDefault(symbol); }

    void handle(const DefParamSymbol& symbol) {
        if (generateDepth <= generateLevel)
            found.push_back(&symbol);
    }

    void handle(const InstanceSymbol& symbol) {
        if (symbol.name.empty() || symbol.body.flags.has(InstanceFlags::Uninstantiated) ||
            hierarchyProblem) {
            return;
        }

        // If we hit max depth we have a problem -- setting the hierarchyProblem
        // member will cause other functions to early out so that we complete
        // this visitation as quickly as possible.
        if (instanceDepth > maxInstanceDepth) {
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

        if (generateDepth >= generateLevel && !inRecursiveInstance)
            return;

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
    size_t generateDepth = 0;
    bool inRecursiveInstance = false;
    const InstanceSymbol* hierarchyProblem = nullptr;
};

// This visitor runs post-elaboration and can be used to find and report on
// things like unused code elements.
struct PostElabVisitor : public ASTVisitor<PostElabVisitor, false, false> {
    explicit PostElabVisitor(Compilation& compilation) : compilation(compilation) {}

    void handle(const InstanceSymbol& symbol) {
        // Ignore instances that have a duplicate body.
        if (!symbol.getCanonicalBody())
            visitDefault(symbol);
    }

    void handle(const NetSymbol& symbol) {
        if (symbol.isImplicit) {
            checkValueUnused(symbol, diag::UnusedImplicitNet, diag::UnusedImplicitNet,
                             diag::UnusedImplicitNet);
        }
        else {
            checkValueUnused(symbol, diag::UnusedNet, diag::UndrivenNet, diag::UnusedButSetNet);
        }
    }

    void handle(const MethodPrototypeSymbol&) {
        // Ignore method prototype arguments, they're not unused.
    }

    void handle(const SubroutineSymbol& symbol) {
        if (symbol.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize)) {
            return;
        }

        visitDefault(symbol);
    }

    void handle(const VariableSymbol& symbol) {
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

    void handle(const ParameterSymbol& symbol) {
        checkValueUnused(symbol, diag::UnusedParameter, {}, diag::UnusedParameter);
    }

    void handle(const TypeParameterSymbol& symbol) {
        checkUnused(symbol, diag::UnusedTypeParameter);
    }

    void handle(const TypeAliasType& symbol) {
        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        {
            auto [used, _] = compilation.isReferenced(*syntax);
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
                    auto [valUsed, _] = compilation.isReferenced(*valSyntax);
                    if (valUsed)
                        return;
                }
            }
        }

        addDiag(symbol, diag::UnusedTypedef);
    }

    void handle(const GenvarSymbol& symbol) { checkUnused(symbol, diag::UnusedGenvar); }

    void handle(const SequenceSymbol& symbol) { checkAssertionDeclUnused(symbol, "sequence"sv); }
    void handle(const PropertySymbol& symbol) { checkAssertionDeclUnused(symbol, "property"sv); }
    void handle(const LetDeclSymbol& symbol) { checkAssertionDeclUnused(symbol, "let"sv); }
    void handle(const CheckerSymbol& symbol) { checkAssertionDeclUnused(symbol, "checker"sv); }

    void handle(const ExplicitImportSymbol& symbol) { checkUnused(symbol, diag::UnusedImport); }

    void handle(const WildcardImportSymbol& symbol) {
        auto syntax = symbol.getSyntax();
        if (!syntax)
            return;

        auto [used, _] = compilation.isReferenced(*syntax);
        if (!used) {
            if (shouldWarn(symbol))
                symbol.getParentScope()->addDiag(diag::UnusedWildcardImport, symbol.location);
        }
    }

private:
    void checkValueUnused(const ValueSymbol& symbol, DiagCode unusedCode,
                          std::optional<DiagCode> unsetCode, std::optional<DiagCode> unreadCode) {
        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [rvalue, lvalue] = compilation.isReferenced(*syntax);

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
        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = compilation.isReferenced(*syntax);
        if (!used)
            addDiag(symbol, code);
    }

    void checkAssertionDeclUnused(const Symbol& symbol, std::string_view kind) {
        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = compilation.isReferenced(*syntax);
        if (!used && shouldWarn(symbol)) {
            symbol.getParentScope()->addDiag(diag::UnusedAssertionDecl, symbol.location)
                << kind << symbol.name;
        }
    }

    bool hasUnusedAttrib(const Symbol& symbol) {
        for (auto attr : compilation.getAttributes(symbol)) {
            if (attr->name == "unused"sv || attr->name == "maybe_unused"sv)
                return attr->getValue().isTrue();
        }
        return false;
    }

    bool shouldWarn(const Symbol& symbol) {
        auto scope = symbol.getParentScope();
        return !scope->isUninstantiated() && scope->asSymbol().kind != SymbolKind::Package &&
               symbol.name != "_"sv && !hasUnusedAttrib(symbol);
    }

    void addDiag(const Symbol& symbol, DiagCode code) {
        if (shouldWarn(symbol))
            symbol.getParentScope()->addDiag(code, symbol.location) << symbol.name;
    }

    Compilation& compilation;
};

InstanceCacheKey::InstanceCacheKey(const InstanceSymbol& symbol) : symbol(&symbol) {
    size_t h = 0;
    hash_combine(h, &symbol.getDefinition());

    for (auto param : symbol.body.getParameters()) {
        if (param->symbol.kind == SymbolKind::Parameter)
            hash_combine(h, param->symbol.as<ParameterSymbol>().getValue().hash());
        else
            hash_combine(h, param->symbol.as<TypeParameterSymbol>().targetType.getType().hash());
    }

    for (auto conn : symbol.getPortConnections()) {
        if (conn->port.kind == SymbolKind::InterfacePort) {
            auto [iface, modport] = conn->getIfaceConn();
            while (iface && iface->kind == SymbolKind::InstanceArray) {
                auto& arr = iface->as<InstanceArraySymbol>();
                if (arr.empty())
                    iface = nullptr;
                else
                    iface = arr.elements[0];
            }

            if (iface) {
                ifaceKeys.emplace_back(iface->as<InstanceSymbol>());
                hash_combine(h, ifaceKeys.back().savedHash);
            }
        }
    }

    savedHash = h;
}

bool InstanceCacheKey::operator==(const InstanceCacheKey& other) const {
    if (savedHash != other.savedHash ||
        &symbol->getDefinition() != &other.symbol->getDefinition() ||
        ifaceKeys.size() != other.ifaceKeys.size()) {
        return false;
    }

    auto lparams = symbol->body.getParameters();
    auto rparams = other.symbol->body.getParameters();
    SLANG_ASSERT(lparams.size() == rparams.size());

    for (size_t i = 0; i < lparams.size(); i++) {
        auto lp = lparams[i];
        auto rp = rparams[i];
        SLANG_ASSERT(lp->symbol.kind == rp->symbol.kind);

        if (lp->symbol.kind == SymbolKind::Parameter) {
            if (lp->symbol.as<ParameterSymbol>().getValue() !=
                rp->symbol.as<ParameterSymbol>().getValue()) {
                return false;
            }
        }
        else {
            auto& lt = lp->symbol.as<TypeParameterSymbol>().targetType.getType();
            auto& rt = rp->symbol.as<TypeParameterSymbol>().targetType.getType();
            if (!lt.isMatching(rt))
                return false;
        }
    }

    for (size_t i = 0; i < ifaceKeys.size(); i++) {
        if (ifaceKeys[i] != other.ifaceKeys[i])
            return false;
    }

    return true;
}

} // namespace slang::ast
