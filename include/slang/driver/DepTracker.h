//------------------------------------------------------------------------------
//! @file DepTracker.h
//! @brief Dependency tracker for SystemVerilog syntax trees.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "slang/syntax/SyntaxTree.h"

class SLANG_EXPORT DepTracker {
    template<typename T>
    using RC = std::shared_ptr<T>;
    using SyntaxTree = slang::syntax::SyntaxTree;

public:
    /// @brief Represents dependency resolution results
    struct Deps {
        /// @brief Either direct dependencies of a module, or transitive dependencies of a request
        std::vector<RC<SyntaxTree>> deps;
        /// @brief Names of modules/symbols that were referenced but not found
        /// This does not always indicate an error, as some modules may be unused or on an untaken
        /// generate branch.
        std::vector<std::string_view> missingNames;
    };

    /// @brief Maps module names to their corresponding syntax trees.
    std::unordered_map<std::string_view, RC<SyntaxTree>> moduleToTree;

    /// @brief Maps syntax trees to their dependencies and missing names.
    std::unordered_map<RC<SyntaxTree>, Deps> treeToDeps;

    /// @brief Maps missing names to the trees that depend on them.
    std::unordered_map<std::string_view, std::vector<RC<SyntaxTree>>> missingNames;

    /// @brief Constructs a dependency tracker and preprocesses provided symbols and
    /// @param syntaxTrees All available syntax trees to analyze for dependencies
    DepTracker(const std::vector<RC<SyntaxTree>>& syntaxTrees);

    /// @brief Gets all transitive dependencies for the given module names.
    /// Returns trees in topological order (dependencies appear before dependents).
    /// Handles circular dependencies gracefully by including all modules in cycles.
    /// If a given module is not found, it will be ignored.
    ///
    /// These operate at the syntax tree level, so:
    /// - unused extra modules in files will still trigger dependencies
    /// - untaken generate branches will still trigger dependencies
    /// @param symbols Module/symbol names to find dependencies for
    /// @return Dependency trees and any unresolved symbol names
    Deps getTreesFor(const std::vector<std::string>& symbols) const;

    /// @brief Gets all transitive dependencies for the given syntax trees.
    /// Returns trees in topological order (dependencies appear before dependents).
    /// @param trees Syntax trees to find dependencies for
    /// @return Dependency trees and any unresolved symbol names
    Deps getTreesFor(const std::vector<RC<SyntaxTree>>& trees) const;

    /// @brief Returns all syntax trees in topological order.
    /// This is equivalent to calling getTreesFor() with all available trees.
    /// @return All trees sorted topologically and any unresolved symbol names
    Deps getAllSorted() const;
};
