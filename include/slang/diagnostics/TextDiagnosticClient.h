//------------------------------------------------------------------------------
//! @file TextDiagnosticClient.h
//! @brief Diagnostic client that formats to a text string
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <string>

#include "slang/diagnostics/DiagnosticClient.h"

namespace fmt {
inline namespace v9 {
enum class terminal_color : uint8_t;
}
} // namespace fmt

namespace slang {

class FormatBuffer;

namespace ast {
class Symbol;
}

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
    void showHierarchyInstance(bool show) { includeHierarchy = show; }

    template<typename TFunc>
    void setSymbolPathCB(TFunc&& func) {
        symbolPathCB = std::forward<TFunc>(func);
    }

    template<typename TFunc>
    static void setDefaultSymbolPathCB(TFunc&& func) {
        defaultSymbolPathCB = std::forward<TFunc>(func);
    }

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
    bool includeHierarchy = true;

    using SymbolPathCB = std::function<std::string(const ast::Symbol&)>;
    SymbolPathCB symbolPathCB;
    static SymbolPathCB defaultSymbolPathCB;

    void formatDiag(SourceLocation loc, span<const SourceRange> ranges, DiagnosticSeverity severity,
                    string_view message, string_view optionName);
};

} // namespace slang
