//------------------------------------------------------------------------------
// TextDiagnosticClient.cpp
// Diagnostic client that formats to a text string.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/TextDiagnosticClient.h"

#include "../text/Formatbuffer.h"

#include "slang/symbols/Symbol.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"

namespace slang {

TextDiagnosticClient::TextDiagnosticClient() : buffer(std::make_unique<FormatBuffer>()) {
}

TextDiagnosticClient::~TextDiagnosticClient() = default;

void TextDiagnosticClient::report(const ReportedDiagnostic& diag) {
    if (diag.shouldShowIncludeStack) {
        SmallVectorSized<SourceLocation, 8> includeStack;
        getIncludeStack(diag.location.buffer(), includeStack);

        // Show the stack in reverse. TODO: make this a reverse iterator
        for (int i = int(includeStack.size()) - 1; i >= 0; i--) {
            SourceLocation loc = includeStack[size_t(i)];
            buffer->format("in file included from {}:{}:\n", sourceManager->getFileName(loc),
                           sourceManager->getLineNumber(loc));
        }
    }

    // Print out the hierarchy where the diagnostic occurred, if we know it.
    auto& od = diag.originalDiagnostic;
    if (od.coalesceCount && od.symbol) {
        if (od.coalesceCount == 1)
            buffer->append("  in instance: "sv);
        else
            buffer->format("  in {} instances, e.g. ", *od.coalesceCount);

        std::string str;
        od.symbol->getHierarchicalPath(str);
        buffer->append(str);
        buffer->append("\n"sv);
    }

    // Get all highlight ranges mapped into the reported location of the diagnostic.
    SmallVectorSized<SourceRange, 8> mappedRanges;
    engine->mapSourceRanges(diag.location, diag.ranges, mappedRanges);

    // Write the diagnostic.
    formatDiag(diag.location, mappedRanges, getSeverityString(diag.severity), diag.formattedMessage,
               engine->getOptionName(diag.originalDiagnostic.code));

    // Write out macro expansions, if we have any, in reverse order.
    for (auto it = diag.expansionLocs.rbegin(); it != diag.expansionLocs.rend(); it++) {
        SourceLocation loc = *it;
        std::string name(sourceManager->getMacroName(loc));
        if (name.empty())
            name = "expanded from here";
        else
            name = fmt::format("expanded from macro '{}'", name);

        SmallVectorSized<SourceRange, 8> macroRanges;
        engine->mapSourceRanges(loc, diag.ranges, macroRanges);
        formatDiag(sourceManager->getFullyOriginalLoc(loc), macroRanges, "note"sv, name, "");
    }
}

void TextDiagnosticClient::clear() {
    buffer->clear();
}

std::string TextDiagnosticClient::getString() const {
    return buffer->str();
}

static void highlightRange(SourceRange range, SourceLocation caretLoc, size_t col,
                           string_view sourceLine, std::string& buffer) {
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

    // finally add the highlight chars
    for (; start != end; start++)
        buffer[start] = '~';
}

void TextDiagnosticClient::formatDiag(SourceLocation loc, span<const SourceRange> ranges,
                                      string_view severity, string_view message,
                                      string_view optionName) {
    if (loc == SourceLocation::NoLocation) {
        buffer->format("{}: {}", severity, message);
        if (!optionName.empty())
            buffer->format(" [-W{}]", optionName);
        buffer->append("\n"sv);
        return;
    }

    size_t col = sourceManager->getColumnNumber(loc);
    buffer->format("{}:{}:{}: {}: {}", sourceManager->getFileName(loc),
                   sourceManager->getLineNumber(loc), col, severity, message);

    if (!optionName.empty())
        buffer->format(" [-W{}]", optionName);

    string_view line = getSourceLine(loc, col);
    if (!line.empty()) {
        buffer->format("\n{}\n", line);

        // Highlight any ranges and print the caret location.
        std::string highlight(std::max(line.length(), col), ' ');

        // handle tabs to get proper alignment on a terminal
        for (size_t i = 0; i < line.length(); ++i) {
            if (line[i] == '\t')
                highlight[i] = '\t';
        }

        for (SourceRange range : ranges)
            highlightRange(range, loc, col, line, highlight);

        highlight[col - 1] = '^';
        highlight.erase(highlight.find_last_not_of(' ') + 1);
        buffer->append(highlight);
    }
    buffer->append("\n"sv);
}

} // namespace slang