//------------------------------------------------------------------------------
//! @file MemoryStats.h
//! @brief Utility for writing report of compiler memory usage
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>
#include <string>

#include "slang/util/Util.h"

namespace slang {
class SourceManager;
}

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {
class Compilation;
}

namespace slang::analysis {
class AnalysisManager;
}

namespace slang::driver {

SLANG_EXPORT void printMemoryStats(const std::string& fileName, const SourceManager& sourceManager,
                                   std::span<const std::shared_ptr<syntax::SyntaxTree>> syntaxTrees,
                                   const ast::Compilation* compilation,
                                   const analysis::AnalysisManager* analysisManager);

}
