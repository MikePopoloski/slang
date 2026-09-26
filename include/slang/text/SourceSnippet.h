//------------------------------------------------------------------------------
//! @file SourceSnippet.h
//! @brief Generating highlighted source snippets.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>
#include <string_view>

#include "slang/slang_export.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"
#include "slang/util/TextStyle.h"

namespace slang {

/// Utility functions to generate highlighted source snippets.
class SLANG_EXPORT SourceSnippet {
public:
    SourceSnippet(std::string_view sourceLine, uint32_t tabStop,
                  std::span<const SourceRange> ranges, SourceLocation caretLoc, size_t col,
                  SmallVectorBase<std::pair<size_t, size_t>>& invalidRanges);

    /// Gets the source snippet line.
    const std::string& getSnippetLine() const { return snippetLine; }

    /// Gets the highlighted line.
    const std::string& getHighlightLine() const { return highlightLine; }

private:
    void highlightRange(SourceRange range, SourceLocation caretLoc, size_t col,
                        std::string_view sourceLine);
    void insertCaret(size_t offset);
    void trimHighlight();
    size_t getColumnForByte(size_t b) const;

    SmallVector<int> byteToColumn;
    std::string snippetLine;
    std::string highlightLine;
};

} // namespace slang
