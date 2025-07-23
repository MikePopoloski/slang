//------------------------------------------------------------------------------
// DepTracker.cpp
// Dependency tracker for SystemVerilog syntax trees.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/DepTracker.h"

DepTracker::DepTracker(const std::vector<RC<SyntaxTree>>& _syntaxTrees) :
    syntaxTrees(_syntaxTrees), sm(_syntaxTrees[0]->sourceManager()) {
    SLANG_ASSERT(!syntaxTrees.empty());
}

void DepTracker::connect() {
    std::unordered_map<RC<SyntaxTree>, std::vector<std::string_view>> localTreeToDeps;

    // populdate moduleToTree and string deps first
    for (auto& tree : syntaxTrees) {
        auto& meta = tree->getMetadata();

        // Record provided names
        for (auto& [n, _] : meta.nodeMap) {
            auto decl = &n->as<slang::syntax::ModuleDeclarationSyntax>();
            std::string_view name = decl->header->name.valueText();
            if (!name.empty())
                moduleToTree.emplace(name, tree);
        }

        for (auto classDecl : meta.classDecls) {
            std::string_view name = classDecl->name.valueText();
            if (!name.empty())
                moduleToTree.emplace(name, tree);
        }

        // Record dependencies
        slang::flat_hash_set<std::string_view> deps;

        // module insts
        for (auto name : meta.globalInstances) {
            deps.emplace(name);
        }

        // classes/packages
        for (auto idName : meta.classPackageNames) {
            std::string_view name = idName->identifier.valueText();
            if (!name.empty()) {
                deps.emplace(name);
            }
        }

        // package imports
        for (auto importDecl : meta.packageImports) {
            for (auto importItem : importDecl->items) {
                std::string_view name = importItem->package.valueText();
                if (!name.empty()) {
                    deps.emplace(name);
                }
            }
        }

        // interface ports
        for (auto intf : meta.interfacePorts) {
            std::string_view name = intf->nameOrKeyword.valueText();
            if (!name.empty()) {
                deps.emplace(name);
            }
        }
        localTreeToDeps.emplace(tree, std::vector<std::string_view>(deps.begin(), deps.end()));
    }

    // Resolve dependencies and check for missing
    for (auto& [tree, deps] : localTreeToDeps) {
        std::vector<RC<SyntaxTree>> depTrees;
        for (auto& depName : deps) {
            auto it = moduleToTree.find(depName);
            if (it != moduleToTree.end()) {
                depTrees.push_back(it->second);
            }
            else {
                missingNames[tree].insert(depName);
            }
        }
        treeToDeps[tree] = std::move(depTrees);
    }
    connected = true;
}

DepTracker::DepResult DepTracker::getTreesFor(const std::vector<std::string>& modules) const {
    SLANG_ASSERT(connected);
    // find trees for modules, then call other method
    std::vector<RC<SyntaxTree>> trees;
    slang::flat_hash_set<std::string_view> missingNamesSet;

    for (auto& name : modules) {
        auto it = moduleToTree.find(name);
        if (it != moduleToTree.end()) {
            trees.push_back(it->second);
        }
        else {
            missingNamesSet.insert(name);
        }
    }

    auto result = getTreesFor(trees);
    result.missingTops.insert(result.missingTops.end(), missingNamesSet.begin(),
                              missingNamesSet.end());
    return result;
}

DepTracker::DepResult DepTracker::getTreesFor(const std::vector<RC<SyntaxTree>>& trees) const {

    SLANG_ASSERT(connected);

    // Build topologically sorted result during traversal
    std::vector<RC<SyntaxTree>> result;
    slang::flat_hash_set<RC<SyntaxTree>> visited;
    slang::flat_hash_set<RC<SyntaxTree>> inProgress;
    slang::flat_hash_set<std::string_view> missingVisited;

    std::function<void(RC<SyntaxTree>)> visit = [&](RC<SyntaxTree> tree) {
        if (visited.count(tree))
            return;

        if (inProgress.count(tree)) {
            // Circular dependency detected - skip to avoid infinite loop
            return;
        }

        inProgress.insert(tree);

        // Collect missing names for this tree
        auto missingIt = missingNames.find(tree);
        if (missingIt != missingNames.end()) {
            for (auto& name : missingIt->second) {
                missingVisited.emplace(name);
            }
        }

        // Visit all dependencies first (ensures topological order)
        auto it = treeToDeps.find(tree);
        if (it != treeToDeps.end()) {
            for (auto& dep : it->second) {
                visit(dep);
            }
        }

        inProgress.erase(tree);
        visited.insert(tree);
        result.push_back(tree); // Add after all dependencies processed
    };

    // Start DFS from requested trees
    for (auto& tree : trees) {
        visit(tree);
    }

    return {std::move(result),
            std::vector<std::string_view>(missingVisited.begin(), missingVisited.end())};
}
