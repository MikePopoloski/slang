//------------------------------------------------------------------------------
//! @file ASTDiagMap.h
//! @brief AST Diagnostic Map
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <tuple>
#include <vector>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/FlatMap.h"

namespace slang::ast {

/// A helper class that maintains a map of issued diagnostics keyed by
/// their code and location to aid in deduplicating diagnostics across
/// an AST hierarchy.
class SLANG_EXPORT ASTDiagMap {
public:
    /// Adds a diagnostic to the map, deduplicating if needed.
    Diagnostic& add(Diagnostic diag, bool& isNew);

    /// Coalesces all issued diagnostics into a set that is ready for presenting.
    /// If the @a sourceManager is provided it will be used to sort the diagnostics.
    Diagnostics coalesce(const SourceManager* sourceManager);

private:
    flat_hash_map<std::tuple<DiagCode, SourceLocation>, std::vector<Diagnostic>> map;
};

} // namespace slang::ast
