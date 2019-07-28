//------------------------------------------------------------------------------
// TextDiagnosticClient.h
// Diagnostic client that formats to a text string.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/DiagnosticClient.h"

namespace slang {

class TextDiagnosticClient : public DiagnosticClient {
public:
    TextDiagnosticClient() {}

    void report(const ReportedDiagnostic& diagnostic) override;

    void clear();
    std::string getString() const;

private:
    FormatBuffer buffer;

    void formatDiag(SourceLocation loc, span<const SourceRange> ranges, string_view severity,
                    string_view message);
};

} // namespace slang