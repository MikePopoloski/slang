//------------------------------------------------------------------------------
//! @file DepTracker.h
//! @brief Dependency tracker for SystemVerilog syntax trees.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <memory>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/FlatMap.h"
#include "slang/util/Util.h"

class DepTracker {
    template<typename T>
    using RC = std::shared_ptr<T>;
    using SyntaxTree = slang::syntax::SyntaxTree;

public:
    std::unordered_map<std::string_view, RC<SyntaxTree>> moduleToTree;

    // deps for each tree
    std::unordered_map<RC<SyntaxTree>, std::vector<RC<SyntaxTree>>> treeToDeps;

    // missing names for each tree
    std::unordered_map<RC<SyntaxTree>, slang::flat_hash_set<std::string_view>> missingNames;

    bool connected = false;

    slang::Diagnostics diags;

    DepTracker(const std::vector<RC<SyntaxTree>>& _syntaxTrees);

    /// Connect all syntax trees upfront.
    void connect();

    struct DepResult {
        std::vector<RC<SyntaxTree>> depTrees;
        std::vector<std::string_view> missingNames;
        std::vector<std::string_view> missingTops;
    };

    DepResult getTreesFor(const std::vector<std::string>& modules) const;

    DepResult getTreesFor(const std::vector<RC<SyntaxTree>>& trees) const;

private:
    const std::vector<RC<SyntaxTree>>& syntaxTrees;
    const slang::SourceManager& sm;
};
