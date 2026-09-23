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

class FormatBuffer;

/// Utility functions to generate highlighted source snippets.
class SLANG_EXPORT SourceSnippet {
public:
    SourceSnippet(std::string_view sourceLine, uint32_t tabStop);

    /// Highlights specified source range in give source line
    void highlightRange(SourceRange range, SourceLocation caretLoc, size_t col,
                        std::string_view sourceLine);

    /// Inserts caret into designated offset
    void insertCaret(size_t offset);

    /// Trims highlighted range.
    void trimHighlight();

    /// Prints source line and highlights source range in given buffer.
    void printTo(FormatBuffer& out, TerminalColor highlightColor, bool leadingNewline = true);

private:
    size_t getColumnForByte(size_t b) const;

    SmallVector<int> byteToColumn;
    SmallVector<std::pair<size_t, size_t>, 4> invalidRanges;
    std::string snippetLine;
    std::string highlightLine;
};

} // namespace slang
