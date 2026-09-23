//------------------------------------------------------------------------------
// SourceSnippet.cpp
// Generating highlighted source snippets.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/text/SourceSnippet.h"

#include "../text/FormatBuffer.h"
#include <ranges>

#include "slang/text/CharInfo.h"

namespace slang {

static bool printableTextForNextChar(std::string_view sourceLine, size_t& index, uint32_t tabStop,
                                     SmallVectorBase<char>& out, size_t& columnWidth) {
    SLANG_ASSERT(index < sourceLine.size());

    // Expand tabs based on tabStop setting.
    if (sourceLine[index] == '\t') {
        // Find number of bytes since previous tab or line beginning.
        uint32_t col = 0;
        size_t i = index;
        while (i > 0) {
            if (sourceLine[--i] == '\t')
                break;
            ++col;
        }

        uint32_t numSpaces = tabStop - col % tabStop;
        SLANG_ASSERT(numSpaces > 0 && numSpaces <= tabStop);
        index++;

        for (uint32_t j = 0; j < numSpaces; j++)
            out.push_back(' ');

        columnWidth = out.size();
        return true;
    }

    auto data = sourceLine.data() + index;
    auto originalData = data;

    // Try to decode the next UTF-8 character we see.
    int error;
    uint32_t c;
    int unused;
    if (index + 4 <= sourceLine.size()) {
        data = utf8Decode(data, &c, &error, unused);
    }
    else {
        char buf[4] = {};
        auto spaceLeft = sourceLine.size() - index;
        memcpy(buf, data, spaceLeft);

        auto next = utf8Decode(buf, &c, &error, unused);
        data += std::min(size_t(next - buf), spaceLeft);
    }

    if (error) {
        // Not valid UTF-8, so print a placeholder instead.
        unsigned char invalid = (unsigned char)sourceLine[index++];
        out.append_range("<XX>"sv);
        out[1] = getHexForDigit(invalid / 16);
        out[2] = getHexForDigit(invalid % 16);
        columnWidth = out.size();
        return false;
    }

    index = size_t(data - sourceLine.data());

    if (!isPrintableUnicode(c)) {
        SmallVector<char, 8> buf;
        do {
            buf.push_back(getHexForDigit(c % 16));
            c /= 16;
        } while (c);

        out.append_range("<U+"sv);
        out.append_range(std::views::reverse(buf));
        out.push_back('>');
        columnWidth = out.size();
        return false;
    }

    // Otherwise this is a normal printable character.
    out.append(originalData, data);
    columnWidth = (size_t)charWidthUnicode(c);
    return true;
}

SourceSnippet::SourceSnippet(std::string_view sourceLine, uint32_t tabStop,
                             std::span<const SourceRange> ranges, SourceLocation caretLoc,
                             size_t col,
                             SmallVectorBase<std::pair<size_t, size_t>>& invalidRanges) {
    SLANG_ASSERT(!sourceLine.empty());

    byteToColumn.resize(sourceLine.size() + 1);
    for (size_t i = 0; i < byteToColumn.size(); i++)
        byteToColumn[i] = -1;

    snippetLine.reserve(sourceLine.size());

    SmallVector<char> buffer;
    size_t column = 0;
    size_t i = 0;
    while (i < sourceLine.size()) {
        byteToColumn[i] = (int)column;

        size_t columnWidth;
        buffer.clear();
        if (!printableTextForNextChar(sourceLine, i, tabStop, buffer, columnWidth))
            invalidRanges.push_back({snippetLine.size(), buffer.size()});

        snippetLine.append(buffer.data(), buffer.size());
        column += columnWidth;
    }

    byteToColumn[sourceLine.size()] = (int)column;
    highlightLine = std::string(column, ' ');

    for (SourceRange range : ranges)
        highlightRange(range, caretLoc, col, sourceLine);

    insertCaret(col);
    trimHighlight();
}

size_t SourceSnippet::getColumnForByte(size_t b) const {
    while (byteToColumn[b] == -1)
        b--;
    return (size_t)byteToColumn[b];
}

void SourceSnippet::highlightRange(SourceRange range, SourceLocation caretLoc, size_t col,
                                   std::string_view sourceLine) {
    // Trim the range so that it only falls on the same line as the cursor
    size_t start = range.start().offset();
    size_t end = range.end().offset();
    size_t startOfLine = caretLoc.offset() - (col - 1);
    size_t endOfLine = startOfLine + sourceLine.length();
    if (start < startOfLine)
        start = startOfLine;
    if (end > endOfLine)
        end = endOfLine;

    if (start >= end)
        return;

    // walk the range in to skip any leading or trailing whitespace
    start -= startOfLine;
    end -= startOfLine;
    while (sourceLine[start] == ' ' || sourceLine[start] == '\t') {
        start++;
        if (start == end)
            return;
    }
    while (sourceLine[end - 1] == ' ' || sourceLine[end - 1] == '\t') {
        end--;
        if (start == end)
            return;
    }

    size_t startCol = getColumnForByte(start);
    size_t endCol = getColumnForByte(end);
    SLANG_ASSERT(startCol <= endCol);

    if (highlightLine.size() < endCol)
        highlightLine.resize(endCol, ' ');

    std::ranges::fill(highlightLine.begin() + ptrdiff_t(startCol),
                      highlightLine.begin() + ptrdiff_t(endCol), '~');
}

void SourceSnippet::insertCaret(size_t offset) {
    size_t column = getColumnForByte(offset - 1);
    if (highlightLine.size() < column + 1)
        highlightLine.resize(column + 1, ' ');
    highlightLine[column] = '^';
}

void SourceSnippet::trimHighlight() {
    highlightLine.erase(highlightLine.find_last_not_of(' ') + 1);
}

} // namespace slang
