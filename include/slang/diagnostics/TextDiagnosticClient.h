//------------------------------------------------------------------------------
//! @file TextDiagnosticClient.h
//! @brief Diagnostic client that formats to a text string
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <fmt/color.h>
#include <string>

#include "slang/diagnostics/DiagnosticClient.h"

namespace slang {

class FormatBuffer;

#define SHPO(x) x(Auto) x(Always) x(Never)
SLANG_ENUM(ShowHierarchyPathOption, SHPO)
#undef SHPO

/// A diagnostic client that serializes diagnostics to human-friendly text format.
class SLANG_EXPORT TextDiagnosticClient : public DiagnosticClient {
public:
    /// The color to use for notes.
    fmt::terminal_color noteColor;

    /// The color to use for warnings.
    fmt::terminal_color warningColor;

    /// The color to use for errors.
    fmt::terminal_color errorColor;

    /// The color to use for fatal errors.
    fmt::terminal_color fatalColor;

    /// The color to use for highlights.
    fmt::terminal_color highlightColor;

    /// The color to use for file names.
    fmt::terminal_color filenameColor;

    /// The color to use for locations.
    fmt::terminal_color locationColor;

    /// Constructs a new TextDiagnosticClient.
    TextDiagnosticClient();
    ~TextDiagnosticClient() override;

    /// Sets whether to use terminal color codes in the output.
    void showColors(bool show);

    /// Sets whether to show column numbers in the output.
    void showColumn(bool show) { includeColumn = show; }

    /// Sets whether to show locations in the output.
    void showLocation(bool show) { includeLocation = show; }

    /// Sets whether to show source line context in the output.
    void showSourceLine(bool show) { includeSource = show; }

    /// Sets whether to show diagnostic option names in the output.
    void showOptionName(bool show) { includeOptionName = show; }

    /// Sets whether to show include file stacks in the output.
    void showIncludeStack(bool show) { includeFileStack = show; }

    /// Sets whether to show macro expansions in the output.
    void showMacroExpansion(bool show) { includeExpansion = show; }

    /// Sets whether to show hierarchy paths in the output.
    void showHierarchyInstance(ShowHierarchyPathOption option) { includeHierarchy = option; }

    /// Gets the terminal color to use for the given diagnostic severity.
    fmt::terminal_color getSeverityColor(DiagnosticSeverity severity) const;

    /// Called by the DiagnosticEngine to report a new diagnostic.
    void report(const ReportedDiagnostic& diagnostic) override;

    /// Clears the serialized text buffer.
    void clear();

    /// Returns true if the text buffer is empty and false otherwise.
    [[nodiscard]] bool empty() const;

    /// Gets the current contents of the serialized text buffer.
    [[nodiscard]] std::string getString() const;

private:
    std::unique_ptr<FormatBuffer> buffer;
    bool includeColumn = true;
    bool includeLocation = true;
    bool includeSource = true;
    bool includeOptionName = true;
    bool includeFileStack = true;
    bool includeExpansion = true;
    ShowHierarchyPathOption includeHierarchy = ShowHierarchyPathOption::Auto;

    void formatDiag(SourceLocation loc, std::span<const SourceRange> ranges,
                    DiagnosticSeverity severity, std::string_view message,
                    std::string_view optionName);
};

} // namespace slang
