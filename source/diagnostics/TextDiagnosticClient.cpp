//------------------------------------------------------------------------------
// TextDiagnosticClient.cpp
// Diagnostic client that formats to a text string.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/TextDiagnosticClient.h"

#include "slang/text/SourceManager.h"

namespace slang {

void TextDiagnosticClient::report(const ReportedDiagnostic& diag) {
    if (diag.shouldShowIncludeStack) {
        SmallVectorSized<SourceLocation, 8> includeStack;
        getIncludeStack(diag.location.buffer(), includeStack);

        // Show the stack in reverse. TODO: make this a reverse iterator
        for (int i = int(includeStack.size()) - 1; i >= 0; i--) {
            SourceLocation loc = includeStack[size_t(i)];
            buffer.format("in file included from {}:{}:\n", sourceManager->getFileName(loc),
                          sourceManager->getLineNumber(loc));
        }
    }

    // Get all highlight ranges mapped into the reported location of the diagnostic.
    SmallVectorSized<SourceRange, 8> mappedRanges;
    engine->mapSourceRanges(diag.location, diag.ranges, mappedRanges);

    // Write the diagnostic.
    formatDiag(diag.location, mappedRanges, getSeverityString(diag.severity),
               diag.formattedMessage);

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
        formatDiag(sourceManager->getFullyOriginalLoc(loc), macroRanges, "note"sv, name);
    }
}

void TextDiagnosticClient::clear() {
    buffer.clear();
}

std::string TextDiagnosticClient::getString() const {
    return buffer.str();
}

static void highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col,
                           string_view sourceLine, std::string& buffer) {
    // Trim the range so that it only falls on the same line as the cursor
    uint32_t start = range.start().offset();
    uint32_t end = range.end().offset();
    uint32_t startOfLine = caretLoc.offset() - (col - 1);
    uint32_t endOfLine = startOfLine + (uint32_t)sourceLine.length();
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
                                      string_view severity, string_view message) {
    uint32_t col = sourceManager->getColumnNumber(loc);
    buffer.format("{}:{}:{}: {}: {}", sourceManager->getFileName(loc),
                  sourceManager->getLineNumber(loc), col, severity, message);

    string_view line = getSourceLine(loc, col);
    if (!line.empty()) {
        buffer.format("\n{}\n", line);

        // Highlight any ranges and print the caret location.
        std::string highlight(std::max(line.length(), (size_t)col), ' ');

        // handle tabs to get proper alignment on a terminal
        for (size_t i = 0; i < line.length(); ++i) {
            if (line[i] == '\t')
                highlight[i] = '\t';
        }

        for (SourceRange range : ranges)
            highlightRange(range, loc, col, line, highlight);

        highlight[col - 1] = '^';
        highlight.erase(highlight.find_last_not_of(' ') + 1);
        buffer.append(highlight);
    }
    buffer.append("\n");
}

} // namespace slang