//------------------------------------------------------------------------------
//! @file TextDiagnosticClient.h
//! @brief Diagnostic client that formats to a text string
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/DiagnosticClient.h"

namespace slang {

class FormatBuffer;

class TextDiagnosticClient : public DiagnosticClient {
public:
    TextDiagnosticClient();
    ~TextDiagnosticClient();

    void setColorsEnabled(bool enabled);

    void report(const ReportedDiagnostic& diagnostic) override;

    void clear();
    std::string getString() const;

private:
    std::unique_ptr<FormatBuffer> buffer;

    void formatDiag(SourceLocation loc, span<const SourceRange> ranges, DiagnosticSeverity severity,
                    string_view message, string_view optionName);
};

} // namespace slang