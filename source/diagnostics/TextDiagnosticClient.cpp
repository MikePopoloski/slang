//------------------------------------------------------------------------------
// TextDiagnosticClient.cpp
// Diagnostic client that formats to a text string
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/TextDiagnosticClient.h"

#include "../text/FormatBuffer.h"
#include <ranges>

#include "slang/text/SourceManager.h"
#include "slang/text/SourceSnippet.h"

namespace slang {

TextDiagnosticClient::TextDiagnosticClient() : buffer(std::make_unique<FormatBuffer>()) {
    noteColor = TerminalColor::BrightBlack;
    warningColor = TerminalColor::BrightYellow;
    errorColor = TerminalColor::BrightRed;
    fatalColor = TerminalColor::BrightRed;
    highlightColor = TerminalColor::BrightGreen;
    filenameColor = TerminalColor::Cyan;
    locationColor = TerminalColor::BrightCyan;
}

TextDiagnosticClient::~TextDiagnosticClient() = default;

void TextDiagnosticClient::showColors(bool show) {
    buffer->setColorsEnabled(show);
}

TerminalColor TextDiagnosticClient::getSeverityColor(DiagnosticSeverity severity) const {
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
            return TerminalColor::Black;
    }
}

void TextDiagnosticClient::report(const ReportedDiagnostic& diag) {
    writeDiagnostic(diag, diag.severity);
    for (auto& note : diag.notes)
        writeDiagnostic(note, DiagnosticSeverity::Note);
}

void TextDiagnosticClient::writeDiagnostic(const ReportedDiagnosticInfo& diag,
                                           DiagnosticSeverity severity) {
    if (diag.shouldShowIncludeStack && includeFileStack) {
        SmallVector<SourceLocation> includeStack;
        getIncludeStack(diag.location.buffer(), includeStack);

        // Show the stack in reverse.
        for (int i = int(includeStack.size()) - 1; i >= 0; i--) {
            SourceLocation loc = includeStack[size_t(i)];
            buffer->format("in file included from {}:{}:\n", getFileName(loc),
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

        buffer->append(TextEmphasis::Bold, symbolPathCB(*od.symbol));
        buffer->append("\n"sv);
    }

    // Get all highlight ranges mapped into the reported location of the diagnostic.
    SmallVector<SourceRange> mappedRanges;
    engine->mapSourceRanges(diag.location, diag.ranges, mappedRanges);

    // Write the diagnostic.
    formatDiag(diag.location, mappedRanges, severity, diag.formattedMessage,
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

bool TextDiagnosticClient::empty() const {
    return buffer->empty();
}

std::string TextDiagnosticClient::getString() const {
    return buffer->str();
}

void TextDiagnosticClient::formatDiag(SourceLocation loc, std::span<const SourceRange> ranges,
                                      DiagnosticSeverity severity, std::string_view message,
                                      std::string_view optionName) {
    constexpr size_t MaxLineLengthToPrint = 4096;

    size_t col = 0;
    bool hasLocation = loc.buffer() != SourceLocation::NoLocation.buffer();
    if (hasLocation) {
        // We always need the byte-based column for use in the source line stuff below.
        col = sourceManager->getColumnNumber(loc);

        if (includeLocation) {
            buffer->append(fg(filenameColor), getFileName(loc));
            buffer->append(":");
            buffer->format(fg(locationColor), "{}", sourceManager->getLineNumber(loc));

            if (includeColumn) {
                // If the user wants "display" column numbers we will adjust that here.
                size_t displayCol = col;
                if (columnUnit == ColumnUnit::Display)
                    displayCol = sourceManager->getDisplayColumnNumber(loc);

                buffer->format(fg(locationColor), ":{}", displayCol);
            }
            buffer->append(": ");
        }

        // Arbitrarily stop showing snippets when the line gets too long.
        if (col > MaxLineLengthToPrint)
            hasLocation = false;
    }

    buffer->format(fg(getSeverityColor(severity)), "{}: ", getSeverityString(severity));

    if (severity != DiagnosticSeverity::Note)
        buffer->format(TextEmphasis::Bold, "{}", message);
    else
        buffer->append(message);

    if (!optionName.empty() && includeOptionName)
        buffer->format(" [-W{}]", optionName);

    if (hasLocation && includeSource) {
        std::string_view line = sourceManager->getSourceLine(loc);
        if (!line.empty() && line.length() < MaxLineLengthToPrint) {
            // We might want to make the tab width configurable at some point,
            // but for now hardcode it to 8 to match the default on basically
            // every terminal.
            SmallVector<std::pair<size_t, size_t>, 4> invalidRanges;
            SourceSnippet snippet(line, 8, ranges, loc, col, invalidRanges);
            buffer->append("\n");

            if (invalidRanges.empty()) {
                buffer->append(snippet.getSnippetLine());
            }
            else {
                size_t index = 0;
                std::string_view view = snippet.getSnippetLine();
                for (auto [start, count] : invalidRanges) {
                    SLANG_ASSERT(start >= index);
                    buffer->append(view.substr(index, start - index));

                    buffer->append(TextEmphasis::Reverse, view.substr(start, count));
                    index = start + count;
                }

                buffer->append(view.substr(index));
            }

            buffer->append("\n");
            buffer->append(fg(highlightColor), snippet.getHighlightLine());
        }
    }

    buffer->append("\n"sv);
}

} // namespace slang
