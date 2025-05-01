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

enum class ShowHierarchyPathOption { Auto, Always, Never };

class SLANG_EXPORT TextDiagnosticClient : public DiagnosticClient {
public:
    fmt::terminal_color noteColor;
    fmt::terminal_color warningColor;
    fmt::terminal_color errorColor;
    fmt::terminal_color fatalColor;
    fmt::terminal_color highlightColor;
    fmt::terminal_color filenameColor;
    fmt::terminal_color locationColor;

    TextDiagnosticClient();
    ~TextDiagnosticClient();

    void showColors(bool show);
    void showColumn(bool show) { includeColumn = show; }
    void showLocation(bool show) { includeLocation = show; }
    void showSourceLine(bool show) { includeSource = show; }
    void showOptionName(bool show) { includeOptionName = show; }
    void showIncludeStack(bool show) { includeFileStack = show; }
    void showMacroExpansion(bool show) { includeExpansion = show; }
    void showHierarchyInstance(ShowHierarchyPathOption option) { includeHierarchy = option; }

    fmt::terminal_color getSeverityColor(DiagnosticSeverity severity) const;

    void report(const ReportedDiagnostic& diagnostic) override;

    void clear();
    std::string getString() const;

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
