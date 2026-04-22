//------------------------------------------------------------------------------
// DefParamReachability.cpp
// CST-level analysis for defparam/bind reachability
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/util/TimeTrace.h"

namespace slang::ast {

using namespace syntax;

namespace {

// Result type for the reachability graph computation.
struct ReachabilityResult {
    flat_hash_set<const SyntaxNode*> reachable;
    flat_hash_set<std::string_view> reachableNames;
};

// A helper class for constructing the set of definitions we need to care
// about when doing defparam and bind resolution.
class ReachbilityGraph {
public:
    static ReachabilityResult compute(
        std::span<const std::shared_ptr<syntax::SyntaxTree>> syntaxTrees) {
        TimeTraceScope timeScope("computeReachability"sv, ""sv);

        ReachbilityGraph graph(syntaxTrees);
        ReachabilityResult result;
        result.reachable = std::move(graph.reachable);
        for (auto& [name, nodes] : graph.nameMap) {
            for (auto node : nodes) {
                if (result.reachable.contains(node)) {
                    result.reachableNames.emplace(name);
                    break;
                }
            }
        }
        return result;
    }

private:
    enum class Reachability { Unknown, Computing, Reachable, NotReachable };

    // Information collected from scanning a single definition's CST.
    struct DefinitionInfo {
        const SyntaxNode* defNode = nullptr;
        SmallVector<std::string_view> instanceNames;
        SmallVector<const SyntaxNode*> nestedDefs;
        Reachability reachability = Reachability::Unknown;
    };

    flat_hash_map<const SyntaxNode*, DefinitionInfo> syntaxMap;
    flat_hash_map<std::string_view, SmallVector<const SyntaxNode*>> nameMap;
    flat_hash_set<const SyntaxNode*> reachable;
    SmallVector<const BindDirectiveSyntax*> bindDirectives;

    ReachbilityGraph(std::span<const std::shared_ptr<syntax::SyntaxTree>> syntaxTrees) {
        // First scan all members, looking for module/interface definitions,
        // defparams, and bind directives. Leaf nodes that directly contain
        // defparams and binds will be marked reachable.
        DefinitionInfo rootInfo;
        for (auto& tree : syntaxTrees)
            scanMembers(tree->root(), rootInfo);

        // Any bind directive that targets a definition unconditionally (or even looks
        // like it does, since we can't be sure for the ambiguous single-name case)
        // will count as edges instantiating the given definition, so that if the bind
        // instance is reachable for defparams, then the target definition is also.
        for (auto bind : bindDirectives) {
            if (!bind->targetInstances && bind->target->kind == SyntaxKind::IdentifierName &&
                bind->instantiation->kind == SyntaxKind::HierarchyInstantiation) {

                // Find the definition(s) this bind is instantiating.
                auto instName = bind->instantiation->as<HierarchyInstantiationSyntax>().type;
                if (auto instIt = nameMap.find(instName.valueText()); instIt != nameMap.end()) {

                    // Find the target definition(s) in which they will be instantiated.
                    auto targetName = bind->target->as<IdentifierNameSyntax>().identifier;
                    if (auto targetIt = nameMap.find(targetName.valueText());
                        targetIt != nameMap.end()) {

                        // Each definition associated with the instance(s) will be
                        // assumed to be an outgoing edge for each target node.
                        for (auto instNode : instIt->second) {
                            for (auto targetNode : targetIt->second) {
                                auto defIt = syntaxMap.find(targetNode);
                                SLANG_ASSERT(defIt != syntaxMap.end());
                                defIt->second.nestedDefs.push_back(instNode);
                            }
                        }
                    }
                }
            }
        }

        // Now transitively mark all definitions that contain reachable instances
        // as reachable themselves.
        for (auto node : rootInfo.nestedDefs) {
            auto it = syntaxMap.find(node);
            SLANG_ASSERT(it != syntaxMap.end());
            checkReachable(it->second);
        }
    }

    // Recursively scan CST members for defparams, binds, and instantiation names.
    void scanMembers(const SyntaxNode& node, DefinitionInfo& info) {
        switch (node.kind) {
            case SyntaxKind::DefParam:
            case SyntaxKind::BindDirective:
                if (info.reachability != Reachability::Reachable) {
                    info.reachability = Reachability::Reachable;
                    reachable.emplace(info.defNode);
                }
                if (node.kind == SyntaxKind::BindDirective)
                    bindDirectives.push_back(&node.as<BindDirectiveSyntax>());
                break;
            case SyntaxKind::HierarchyInstantiation: {
                auto name = node.as<HierarchyInstantiationSyntax>().type.valueText();
                if (!name.empty())
                    info.instanceNames.push_back(name);
                break;
            }
            case SyntaxKind::IfGenerate: {
                auto& ifGen = node.as<IfGenerateSyntax>();
                scanMembers(*ifGen.block, info);
                if (ifGen.elseClause)
                    scanMembers(*ifGen.elseClause->clause, info);
                break;
            }
            case SyntaxKind::CaseGenerate: {
                auto& caseGen = node.as<CaseGenerateSyntax>();
                for (auto item : caseGen.items) {
                    if (item->kind == SyntaxKind::StandardCaseItem)
                        scanMembers(*item->as<StandardCaseItemSyntax>().clause, info);
                    else if (item->kind == SyntaxKind::DefaultCaseItem)
                        scanMembers(*item->as<DefaultCaseItemSyntax>().clause, info);
                }
                break;
            }
            case SyntaxKind::LoopGenerate:
                scanMembers(*node.as<LoopGenerateSyntax>().block, info);
                break;
            case SyntaxKind::GenerateBlock:
                for (auto member : node.as<GenerateBlockSyntax>().members)
                    scanMembers(*member, info);
                break;
            case SyntaxKind::GenerateRegion:
                for (auto member : node.as<GenerateRegionSyntax>().members)
                    scanMembers(*member, info);
                break;
            case SyntaxKind::CompilationUnit:
                for (auto member : node.as<CompilationUnitSyntax>().members)
                    scanMembers(*member, info);
                break;
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration: {
                auto& decl = node.as<ModuleDeclarationSyntax>();
                auto name = decl.header->name.valueText();
                if (!name.empty()) {
                    info.nestedDefs.push_back(&node);

                    DefinitionInfo childInfo;
                    childInfo.defNode = &node;
                    for (auto child : decl.members)
                        scanMembers(*child, childInfo);

                    syntaxMap.emplace(&node, std::move(childInfo));
                    nameMap[name].push_back(&node);
                }
                break;
            }
            default:
                break;
        }
    }

    // Compute transitive reachability via DFS.
    bool checkReachable(DefinitionInfo& info) {
        switch (info.reachability) {
            case Reachability::Reachable:
                return true;
            case Reachability::NotReachable:
                return false;
            case Reachability::Computing:
                // This is a cycle, not reachable through this path.
                return false;
            default:
                break;
        }

        info.reachability = Reachability::Computing;

        auto checkChildren = [&](SmallVector<const SyntaxNode*>& children) {
            for (auto child : children) {
                auto childIt = syntaxMap.find(child);
                SLANG_ASSERT(childIt != syntaxMap.end());

                if (checkReachable(childIt->second)) {
                    info.reachability = Reachability::Reachable;
                    reachable.emplace(info.defNode);
                    return true;
                }
            }
            return false;
        };

        for (auto& name : info.instanceNames) {
            if (auto it = nameMap.find(name); it != nameMap.end()) {
                if (checkChildren(it->second))
                    return true;
            }
        }

        if (checkChildren(info.nestedDefs))
            return true;

        info.reachability = Reachability::NotReachable;
        return false;
    }
};

// Tracks the set of instance paths targeted by bind directives whose bound
// module is known to contain defparams or binds.
class ActiveTargetedBinds {
public:
    void add(const OpaqueInstancePath& path) {
        Node* node = &root;
        for (auto& entry : path.entries)
            node = &node->childNodes[entry];
    }

    [[nodiscard]] bool contains(const Symbol& symbol) const {
        const Node* node = &root;
        OpaqueInstancePath path(symbol);
        for (auto& entry : path.entries) {
            auto it = node->childNodes.find(entry);
            if (it == node->childNodes.end())
                return false;

            node = &it->second;
        }

        return true;
    }

private:
    struct Node {
        flat_hash_map<OpaqueInstancePath::Entry, Node> childNodes;
    };

    Node root;
};

const ConfigBlockSymbol::InstanceOverride* getConfigInstanceOverrideNode(
    const InstanceSymbol& symbol, const ResolvedConfig& resolvedConfig) {

    auto& instOverrides = resolvedConfig.useConfig.getInstanceOverrides();
    if (instOverrides.empty())
        return nullptr;

    const Scope* scope = &symbol.body;
    SmallVector<const Symbol*> parentStack;
    while (true) {
        auto sym = &scope->asSymbol();
        if (sym->kind == SymbolKind::InstanceBody) {
            sym = sym->as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(sym);
        }

        parentStack.push_back(sym);

        scope = sym->getParentScope();
        if (!scope || &resolvedConfig.rootInstance == sym)
            break;
    }

    if (parentStack.empty() || parentStack.back() != &resolvedConfig.rootInstance)
        return nullptr;

    auto rootIt = instOverrides.find(resolvedConfig.rootInstance.getDefinition().name);
    if (rootIt == instOverrides.end())
        return nullptr;

    auto node = &rootIt->second;
    for (size_t i = parentStack.size() - 1; i > 0; i--) {
        auto childIt = node->childNodes.find(parentStack[i - 1]->name);
        if (childIt == node->childNodes.end())
            return nullptr;

        node = &childIt->second;
    }

    return node;
}

// Returns true if the given config instance-override subtree has any rule
// that targets a module known to contain defparams or binds.
static bool hasReachableInstanceOverride(const ConfigBlockSymbol::InstanceOverride& node,
                                         const flat_hash_set<std::string_view>& reachableNames) {
    for (auto& [name, child] : node.childNodes) {
        if (child.rule && !child.rule->useCell.name.empty()) {
            // Targeting a config block: be conservative and assume relevant.
            if (child.rule->useCell.targetConfig)
                return true;

            // If the replacement module is reachable, we need to descend.
            if (reachableNames.contains(child.rule->useCell.name))
                return true;

            // The replacement is not reachable so this whole subtree can
            // never expose defparams or binds -- skip it.
            continue;
        }

        // No module substitution (liblist/params only, or no rule): recurse
        // to look for deeper overrides that might name a reachable module.
        if (hasReachableInstanceOverride(child, reachableNames))
            return true;
    }
    return false;
}

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
struct DefParamVisitor : public ASTVisitor<DefParamVisitor> {
    DefParamVisitor(size_t maxInstanceDepth, size_t maxBlocks, size_t generateLevel,
                    const ReachabilityResult& reachabilityResult,
                    const ActiveTargetedBinds& activeTargetedBinds) :
        reachabilityResult(reachabilityResult), activeTargetedBinds(activeTargetedBinds),
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

        // Check whether we can skip visiting this subtree completely, if we know
        // that there will never be a defparam or bind within it.
        if (!shouldVisit(symbol))
            return;

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
    const ReachabilityResult& reachabilityResult;
    const ActiveTargetedBinds& activeTargetedBinds;
    size_t instanceDepth = 0;
    size_t maxInstanceDepth = 0;
    size_t generateLevel = 0;
    size_t numBlocksSeen = 0;
    size_t maxBlocks = 0;
    size_t generateDepth = 0;
    bool inRecursiveInstance = false;
    bool skippedAnything = false;
    const InstanceSymbol* hierarchyProblem = nullptr;

private:
    struct CachedConfigReachability {
        bool hasCellOverride = false;
        bool hasInstOverride = false;
    };

    mutable flat_hash_map<const ConfigBlockSymbol*, CachedConfigReachability> configCache;

    bool shouldVisit(const InstanceSymbol& symbol) const {
        // If we know this subtree has defparams or binds, keep going.
        if (reachabilityResult.reachable.contains(symbol.getDefinition().getSyntax()))
            return true;

        // If there are active binds that target this instance path
        // and we know they instantiate a module that contains defparams
        // or binds, keep going.
        if (activeTargetedBinds.contains(symbol))
            return true;

        // If there is an active configuration we need to check the overrides.
        if (symbol.resolvedConfig) {
            // Look up (or compute) per-config reachability for cell and instance overrides.
            auto& config = symbol.resolvedConfig->useConfig;
            auto [it, inserted] = configCache.emplace(&config, CachedConfigReachability{});
            if (inserted) {
                auto checkRule = [&](std::string_view cellName, const ConfigRule* rule) {
                    if (!rule)
                        return false;

                    auto& useCell = rule->useCell;
                    if (!useCell.name.empty()) {
                        // Targeting a config block: be conservative.
                        if (useCell.targetConfig)
                            return true;
                        return reachabilityResult.reachableNames.contains(useCell.name);
                    }

                    // liblist/param-only: the same module is instantiated.
                    return reachabilityResult.reachableNames.contains(cellName);
                };

                for (auto& [cellName, override] : config.getCellOverrides()) {
                    if (checkRule(cellName, override.defaultRule)) {
                        it->second.hasCellOverride = true;
                        break;
                    }

                    for (auto& [_, rule] : override.specificLibRules) {
                        if (checkRule(cellName, rule)) {
                            it->second.hasCellOverride = true;
                            break;
                        }
                    }

                    if (it->second.hasCellOverride)
                        break;
                }

                for (auto& [_, rootNode] : config.getInstanceOverrides()) {
                    if (hasReachableInstanceOverride(rootNode, reachabilityResult.reachableNames)) {
                        it->second.hasInstOverride = true;
                        break;
                    }
                }
            }

            if (it->second.hasCellOverride)
                return true;

            if (it->second.hasInstOverride) {
                if (auto node = getConfigInstanceOverrideNode(symbol, *symbol.resolvedConfig)) {
                    if (hasReachableInstanceOverride(*node, reachabilityResult.reachableNames))
                        return true;
                }
            }
        }

        // Otherwise we can skip the instance and all of its children.
        return false;
    }
};

} // namespace

void Compilation::resolveDefParamsAndBinds() {
    TimeTraceScope timeScope("resolveDefParamsAndBinds"sv, ""sv);

    // Compute CST-level reachability so we can later skip definitions that
    // can't contain defparams or bind directives.
    auto reachabilityResult = ReachbilityGraph::compute(syntaxTrees);

    struct OverrideEntry {
        OpaqueInstancePath path;
        const SyntaxNode* targetSyntax = nullptr;
        const SyntaxNode* defparamSyntax = nullptr;
        ConstantValue value;
        std::string pathStr;
    };
    SmallVector<OverrideEntry, 4> overrides;

    struct BindEntry {
        OpaqueInstancePath path;
        const ModuleDeclarationSyntax* definitionTarget = nullptr;
        BindDirectiveInfo info;
    };
    SmallVector<BindEntry> binds;

    auto getActiveTargetedBinds = [&] {
        ActiveTargetedBinds result;
        for (auto& entry : binds) {
            if (!entry.definitionTarget && entry.info.instantiationDefSyntax &&
                reachabilityResult.reachable.contains(entry.info.instantiationDefSyntax)) {
                result.add(entry.path);
            }
        }
        return result;
    };

    auto getNodeFor = [](const OpaqueInstancePath& path, Compilation& c) {
        HierarchyOverrideNode* node = &c.hierarchyOverrides;
        for (auto& entry : path.entries)
            node = &node->childNodes[entry];
        return node;
    };

    auto copyStateInto = [&](Compilation& c, bool isFinal) {
        for (auto& entry : overrides) {
            if (!entry.targetSyntax)
                continue;

            SLANG_ASSERT(entry.defparamSyntax);

            auto node = getNodeFor(entry.path, c);
            auto [it, inserted] = node->paramOverrides.emplace(
                entry.targetSyntax,
                HierarchyOverrideNode::ParamOverride{entry.value, nullptr, entry.defparamSyntax});

            if (!inserted && isFinal) {
                SLANG_ASSERT(it->second.defparam);
                auto& diag = c.root->addDiag(diag::DuplicateDefparam,
                                             entry.defparamSyntax->sourceRange());
                diag.addNote(diag::NotePreviousDefinition, it->second.defparam->sourceRange());
            }
        }

        for (auto& entry : binds) {
            if (entry.definitionTarget) {
                if (!entry.path.empty()) {
                    // This is a nested definition, so we need to put the
                    // bind into the override node.
                    auto node = getNodeFor(entry.path, c);
                    node->binds.push_back({entry.info, entry.definitionTarget});
                }
                else {
                    auto def = c.getDefinition(*c.root, *entry.definitionTarget);
                    if (def) {
                        // const_cast is fine; we accessed the private data of the compilation
                        // through a public interface that added the const on top.
                        const_cast<DefinitionSymbol*>(def)->bindDirectives.push_back(entry.info);
                    }
                }
            }
            else {
                auto node = getNodeFor(entry.path, c);
                node->binds.push_back({entry.info, nullptr});
            }
        }
    };

    auto cloneInto = [&](Compilation& c) {
        c.diagsDisabled = true;
        c.options = options;
        for (auto& tree : syntaxTrees)
            c.addSyntaxTree(tree);

        copyStateInto(c, false);
    };

    auto saveState = [&](DefParamVisitor& visitor, Compilation& c) {
        overrides.clear();
        for (auto defparam : visitor.found) {
            auto target = defparam->getTarget();
            if (!target) {
                overrides.emplace_back();
            }
            else {
                overrides.push_back({OpaqueInstancePath(*target), target->getSyntax(),
                                     defparam->getSyntax(), defparam->getValue(),
                                     target->getHierarchicalPath()});
            }
        }

        // We make a copy of the bind directives list here because resolveBindTargets
        // can cause the compilation to add more entries to the list (for recursive
        // module instantiations).
        binds.clear();
        auto bindDirs = c.bindDirectives;
        for (auto [syntax, scope] : bindDirs) {
            ResolvedBind resolvedBind;
            c.resolveBindTargets(*syntax, *scope, resolvedBind);

            BindDirectiveInfo info;
            info.bindSyntax = syntax;

            auto& def = resolvedBind.instanceDef;
            info.configRuleSyntax = def.configRule ? def.configRule->syntax.get() : nullptr;
            info.configBlockSyntax = def.configRoot ? def.configRoot->getSyntax() : nullptr;
            info.instantiationDefSyntax = def.definition ? def.definition->getSyntax() : nullptr;
            info.isNewConfigRoot = def.configRoot != nullptr;
            if (!info.isNewConfigRoot && resolvedBind.resolvedConfig) {
                info.configBlockSyntax = resolvedBind.resolvedConfig->useConfig.getSyntax();

                // Make a copy of the list; the memory for it is owned by
                // the old compilation that is going away.
                info.liblist = copyFrom(resolvedBind.resolvedConfig->liblist);
            }

            for (auto target : resolvedBind.instTargets)
                binds.emplace_back(BindEntry{OpaqueInstancePath(*target), nullptr, info});

            if (auto defTarget = resolvedBind.defTarget) {
                auto parentScope = defTarget->getParentScope();
                auto defSyntax = defTarget->getSyntax();
                SLANG_ASSERT(parentScope && defSyntax);

                // If this is a nested definition we'll put it into the
                // override node of the parent scope that contains the
                // definition. Otherwise it's a globally targeted bind.
                OpaqueInstancePath path;
                auto& parentSym = parentScope->asSymbol();
                if (parentSym.kind != SymbolKind::CompilationUnit)
                    path = OpaqueInstancePath(parentSym);

                binds.emplace_back(
                    BindEntry{std::move(path), &defSyntax->as<ModuleDeclarationSyntax>(), info});
            }
        }
    };

    auto checkProblem = [&](const DefParamVisitor& visitor) {
        if (visitor.hierarchyProblem) {
            auto& diag = root->addDiag(diag::MaxInstanceDepthExceeded,
                                       visitor.hierarchyProblem->location);
            diag << visitor.hierarchyProblem->getDefinition().getKindString();
            diag << options.maxInstanceDepth;
            sawFatalError = true;
            return true;
        }
        return false;
    };

    // [23.10.4.1] gives an algorithm for elaboration in the face of defparams.
    // Specifically, we need to resolve all possible defparams at one "level" of
    // hierarchy before moving on to a deeper level, where a "level" in this case
    // is each successive set of nested generate blocks.
    size_t generateLevel = 0;
    size_t numBlocksSeen = 0;
    size_t numBindsSeen = 0;
    size_t numDefParamsSeen = 0;
    while (true) {
        // Traverse the design and find all defparams and their values.
        // defparam resolution happens in a cloned compilation unit because we will be
        // constantly mucking with parameter values in ways that can change the actual
        // hierarchy that gets instantiated. Cloning lets us do that in an isolated context
        // and throw that work away once we know the final parameter values.
        size_t currBlocksSeen;
        auto nextIt = [&] {
            // If we haven't found any new blocks we're done iterating.
            SLANG_ASSERT(currBlocksSeen >= numBlocksSeen);
            if (currBlocksSeen == numBlocksSeen)
                return true;

            // Otherwise advance into the next blocks and try again.
            generateLevel++;
            numBlocksSeen = currBlocksSeen;
            return false;
        };

        {
            Compilation initialClone({}, defaultLibPtr);
            cloneInto(initialClone);
            auto activeTargetedBinds = getActiveTargetedBinds();

            while (true) {
                DefParamVisitor v(options.maxInstanceDepth, options.maxDefParamBlocks,
                                  generateLevel, reachabilityResult, activeTargetedBinds);
                initialClone.getRoot(/* skipDefParamsAndBinds */ true).visit(v);
                if (checkProblem(v))
                    return;

                currBlocksSeen = v.numBlocksSeen;
                if (v.found.size() > numDefParamsSeen ||
                    initialClone.bindDirectives.size() > numBindsSeen) {
                    numDefParamsSeen = v.found.size();
                    saveState(v, initialClone);
                    break;
                }

                // We didn't find any more binds or defparams so increase
                // our generate level and try again.
                if (nextIt() || !v.skippedAnything) {
                    saveState(v, initialClone);
                    break;
                }
            }

            // If we have found more binds, do another visit to let them be applied
            // and potentially add blocks and defparams to our set for this level.
            if (initialClone.bindDirectives.size() > numBindsSeen) {
                // Reset the number of defparams seen to ensure that
                // we re-resolve everything after the next iteration.
                numDefParamsSeen = 0;
                numBindsSeen = initialClone.bindDirectives.size();
                continue;
            }
        } // initialClone freed here

        // If we found no defparams we're done.
        if (numDefParamsSeen == 0)
            break;

        // defparams can change the value of parameters, further affecting the value of
        // other defparams elsewhere in the design. This means we need to iterate,
        // reevaluating defparams until they all settle to a stable value or until we
        // give up due to the potential of cyclical references.
        bool allSame = true;
        for (uint32_t i = 0; i < options.maxDefParamSteps; i++) {
            Compilation c({}, defaultLibPtr);
            cloneInto(c);
            auto activeTargetedBinds = getActiveTargetedBinds();

            DefParamVisitor v(options.maxInstanceDepth, options.maxDefParamBlocks, generateLevel,
                              reachabilityResult, activeTargetedBinds);
            c.getRoot(/* skipDefParamsAndBinds */ true).visit(v);
            if (checkProblem(v))
                return;

            // We're only done if we have the same set of defparams with the same set of values.
            allSame = true;
            SLANG_ASSERT(v.found.size() == overrides.size());
            for (size_t j = 0; j < v.found.size(); j++) {
                // Check that the defparam resolved to the same target we saw previously.
                // The spec declares it to be an error if a defparam target changes based
                // on elaboration of other defparam values.
                const SyntaxNode* targetNode = nullptr;
                auto target = v.found[j]->getTarget();
                if (target)
                    targetNode = target->getSyntax();

                auto getRange = [&] {
                    auto syntax = v.found[j]->getSyntax();
                    SLANG_ASSERT(syntax);
                    return syntax->sourceRange();
                };

                auto& prevEntry = overrides[j];
                if (prevEntry.targetSyntax && targetNode && prevEntry.targetSyntax != targetNode) {
                    auto& diag = root->addDiag(diag::DefParamTargetChange, getRange());
                    diag << prevEntry.pathStr;
                    diag << target->getHierarchicalPath();
                    return;
                }

                if (prevEntry.value != v.found[j]->getValue()) {
                    allSame = false;
                    if (i == options.maxDefParamSteps - 1)
                        root->addDiag(diag::DefParamCycle, getRange());
                    break;
                }
            }

            if (allSame)
                break;

            saveState(v, c);
        }

        // If we gave up due to a potential infinite loop, continue exiting.
        if (!allSame)
            break;

        if (nextIt())
            break;
    }

    // We have our final overrides; copy them into the main compilation unit.
    copyStateInto(*this, true);
}

} // namespace slang::ast
