//------------------------------------------------------------------------------
// TextDiagnosticClient.cpp
// Diagnostic client that formats to a text string
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/TextDiagnosticClient.h"

#include <ranges>

#include "slang/text/CharInfo.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/SourceManager.h"

namespace slang {

TextDiagnosticClient::TextDiagnosticClient() : buffer(std::make_unique<FormatBuffer>()) {
    noteColor = fmt::terminal_color::bright_black;
    warningColor = fmt::terminal_color::bright_yellow;
    errorColor = fmt::terminal_color::bright_red;
    fatalColor = fmt::terminal_color::bright_red;
    highlightColor = fmt::terminal_color::bright_green;
    filenameColor = fmt::terminal_color::cyan;
    locationColor = fmt::terminal_color::bright_cyan;
}

TextDiagnosticClient::~TextDiagnosticClient() = default;

void TextDiagnosticClient::showColors(bool show) {
    buffer->setColorsEnabled(show);
}

fmt::terminal_color TextDiagnosticClient::getSeverityColor(DiagnosticSeverity severity) const {
    switch (severity) {
        case DiagnosticSeverity::Note:
            return noteColor;
        case DiagnosticSeverity::Warning:
            return warningColor;
        case DiagnosticSeverity::Error:
            return errorColor;
        case DiagnosticSeverity::Fatal:
            return fatalColor;
        default:
            return fmt::terminal_color::black;
    }
}

void TextDiagnosticClient::report(const ReportedDiagnostic& diag) {
    if (diag.shouldShowIncludeStack && includeFileStack) {
        SmallVector<SourceLocation> includeStack;
        getIncludeStack(diag.location.buffer(), includeStack);

        // Show the stack in reverse.
        for (int i = int(includeStack.size()) - 1; i >= 0; i--) {
            SourceLocation loc = includeStack[size_t(i)];
            buffer->format("in file included from {}:{}:\n", sourceManager->getFileName(loc),
                           sourceManager->getLineNumber(loc));
        }
    }

    // Print out the hierarchy where the diagnostic occurred, if we know it.
    auto& od = diag.originalDiagnostic;
    auto& symbolPathCB = engine->getSymbolPathCB();
    if (od.symbol && symbolPathCB &&
        (includeHierarchy == ShowHierarchyPathOption::Always ||
         (includeHierarchy == ShowHierarchyPathOption::Auto && od.coalesceCount))) {
        if (!od.coalesceCount || od.coalesceCount == 1u)
            buffer->append("  in instance: "sv);
        else
            buffer->format("  in {} instances, e.g. ", *od.coalesceCount);

        buffer->append(fmt::emphasis::bold, symbolPathCB(*od.symbol));
        buffer->append("\n"sv);
    }

    // Get all highlight ranges mapped into the reported location of the diagnostic.
    SmallVector<SourceRange> mappedRanges;
    engine->mapSourceRanges(diag.location, diag.ranges, mappedRanges);

    // Write the diagnostic.
    formatDiag(diag.location, mappedRanges, diag.severity, diag.formattedMessage,
               engine->getOptionName(diag.originalDiagnostic.code));

    // Write out macro expansions, if we have any, in reverse order.
    if (includeExpansion) {
        for (auto it = diag.expansionLocs.rbegin(); it != diag.expansionLocs.rend(); it++) {
            SourceLocation loc = *it;
            std::string name(sourceManager->getMacroName(loc));
            if (name.empty())
                name = "expanded from here";
            else
                name = fmt::format("expanded from macro '{}'", name);

            SmallVector<SourceRange> macroRanges;
            engine->mapSourceRanges(loc, diag.ranges, macroRanges);
            formatDiag(sourceManager->getFullyOriginalLoc(loc), macroRanges,
                       DiagnosticSeverity::Note, name, "");
        }
    }
}

void TextDiagnosticClient::clear() {
    buffer->clear();
}

std::string TextDiagnosticClient::getString() const {
    return buffer->str();
}

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

struct SourceSnippet {
    SourceSnippet(std::string_view sourceLine, uint32_t tabStop) {
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
    }

    size_t getColumnForByte(size_t b) const {
        while (byteToColumn[b] == -1)
            b--;
        return (size_t)byteToColumn[b];
    }

    void highlightRange(SourceRange range, SourceLocation caretLoc, size_t col,
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

    void insertCaret(size_t offset) {
        size_t column = getColumnForByte(offset - 1);
        if (highlightLine.size() < column + 1)
            highlightLine.resize(column + 1, ' ');
        highlightLine[column] = '^';
    }

    void trimHighlight() { highlightLine.erase(highlightLine.find_last_not_of(' ') + 1); }

    void printTo(FormatBuffer& out, fmt::terminal_color highlightColor) {
        out.append("\n");

        if (invalidRanges.empty()) {
            out.append(snippetLine);
        }
        else {
            size_t index = 0;
            std::string_view view = snippetLine;
            for (auto [start, count] : invalidRanges) {
                SLANG_ASSERT(start >= index);
                out.append(view.substr(index, start - index));

                out.append(fmt::emphasis::reverse, view.substr(start, count));
                index = start + count;
            }

            out.append(view.substr(index));
        }

        out.append("\n");
        out.append(fg(highlightColor), highlightLine);
    }

    SmallVector<int> byteToColumn;
    SmallVector<std::pair<size_t, size_t>, 4> invalidRanges;
    std::string snippetLine;
    std::string highlightLine;
};

void TextDiagnosticClient::formatDiag(SourceLocation loc, std::span<const SourceRange> ranges,
                                      DiagnosticSeverity severity, std::string_view message,
                                      std::string_view optionName) {
    constexpr size_t MaxLineLengthToPrint = 4096;

    size_t col = 0;
    bool hasLocation = loc.buffer() != SourceLocation::NoLocation.buffer();
    if (hasLocation) {
        col = sourceManager->getColumnNumber(loc);
        if (includeLocation) {
            buffer->append(fg(filenameColor), sourceManager->getFileName(loc));
            buffer->append(":");
            buffer->format(fg(locationColor), "{}", sourceManager->getLineNumber(loc));
            if (includeColumn)
                buffer->format(fg(locationColor), ":{}", col);
            buffer->append(": ");
        }

        // Arbitrarily stop showing snippets when the line gets too long.
        if (col > MaxLineLengthToPrint)
            hasLocation = false;
    }

    buffer->format(fg(getSeverityColor(severity)), "{}: ", getSeverityString(severity));

    if (severity != DiagnosticSeverity::Note)
        buffer->format(fmt::text_style(fmt::emphasis::bold), "{}", message);
    else
        buffer->append(message);

    if (!optionName.empty() && includeOptionName)
        buffer->format(" [-W{}]", optionName);

    if (hasLocation && includeSource) {
        std::string_view line = getSourceLine(loc, col);
        if (!line.empty() && line.length() < MaxLineLengthToPrint) {
            // We might want to make the tab width configurable at some point,
            // but for now hardcode it to 8 to match the default on basically
            // every terminal.
            SourceSnippet snippet(line, 8);
            for (SourceRange range : ranges)
                snippet.highlightRange(range, loc, col, line);

            snippet.insertCaret(col);
            snippet.trimHighlight();
            snippet.printTo(*buffer, highlightColor);
        }
    }

    buffer->append("\n"sv);
}

} // namespace slang
