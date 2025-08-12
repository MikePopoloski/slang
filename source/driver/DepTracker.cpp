//------------------------------------------------------------------------------
// DepTracker.cpp
// Dependency tracker for SystemVerilog syntax trees.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/DepTracker.h"

DepTracker::DepTracker(const std::vector<RC<SyntaxTree>>& syntaxTrees) {

    std::unordered_map<RC<SyntaxTree>, std::vector<std::string_view>> localTreeToDeps;

    // populdate moduleToTree and string deps first
    for (auto& tree : syntaxTrees) {
        auto& meta = tree->getMetadata();

        // Record provided names using new ParserMetadata method
        for (auto name : meta.getDeclaredSymbols()) {
            moduleToTree.emplace(name, tree);
        }

        // Record dependencies using new ParserMetadata method
        localTreeToDeps.emplace(tree, meta.getReferencedSymbols());
    }

    // Resolve dependencies and check for missing
    for (auto& [tree, deps] : localTreeToDeps) {
        std::vector<RC<SyntaxTree>> depTrees;
        slang::flat_hash_set<std::string_view> missingDeps;
        for (auto& depName : deps) {
            auto it = moduleToTree.find(depName);
            if (it != moduleToTree.end()) {
                depTrees.push_back(it->second);
            }
            else {
                missingNames[depName].push_back(tree);
                missingDeps.emplace(depName);
            }
        }
        treeToDeps[tree] = {
            .deps = std::move(depTrees),
            .missingNames = std::vector<std::string_view>(missingDeps.begin(), missingDeps.end()),
        };
    }
}

DepTracker::Deps DepTracker::getTreesFor(const std::vector<std::string>& symbols) const {
    // find trees for modules, then call other method
    std::vector<RC<SyntaxTree>> trees;
    slang::flat_hash_set<std::string_view> missingNamesSet;

    for (auto& name : symbols) {
        auto it = moduleToTree.find(name);
        if (it != moduleToTree.end()) {
            trees.push_back(it->second);
        }
    }

    auto result = getTreesFor(trees);
    return result;
}

DepTracker::Deps DepTracker::getTreesFor(const std::vector<RC<SyntaxTree>>& trees) const {

    // Build topologically sorted result during traversal
    std::vector<RC<SyntaxTree>> result;
    std::vector<std::string_view> missing;

    slang::flat_hash_set<RC<SyntaxTree>> visited;
    slang::flat_hash_set<RC<SyntaxTree>> inProgress;

    std::function<void(RC<SyntaxTree>)> visit = [&](RC<SyntaxTree> tree) {
        if (visited.count(tree))
            return;

        if (inProgress.count(tree)) {
            // Circular dependency check
            return;
        }

        inProgress.insert(tree);

        auto it = treeToDeps.find(tree);
        if (it != treeToDeps.end()) {
            for (auto& dep : it->second.deps) {
                visit(dep);
            }
            missing.insert(missing.end(), it->second.missingNames.begin(),
                           it->second.missingNames.end());
        }

        inProgress.erase(tree);
        visited.insert(tree);
        // Add after all dependencies processed
        result.push_back(tree);
    };

    // Start DFS from requested trees
    for (auto& tree : trees) {
        visit(tree);
    }

    return {
        result,
        missing,
    };
}

DepTracker::Deps DepTracker::getAllSorted() const {
    std::vector<RC<SyntaxTree>> allTrees;
    allTrees.reserve(treeToDeps.size());
    for (const auto& [tree, _] : treeToDeps) {
        allTrees.push_back(tree);
    }
    return getTreesFor(allTrees);
}
