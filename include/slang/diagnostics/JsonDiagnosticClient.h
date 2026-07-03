//------------------------------------------------------------------------------
//! @file JsonDiagnosticClient.h
//! @brief Diagnostic client that formats to JSON
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/diagnostics/DiagnosticClient.h"

namespace slang {

class JsonWriter;

/// A diagnostic client that serializes each diagnostic to JSON format.
class SLANG_EXPORT JsonDiagnosticClient : public DiagnosticClient {
public:
    /// Constructs a new JsonDiagnosticClient that outputs to the given JsonWriter.
    JsonDiagnosticClient(JsonWriter& writer) : writer(writer) {}

    /// Called by the DiagnosticEngine to report a new diagnostic.
    void report(const ReportedDiagnostic& diagnostic) override;

private:
    JsonWriter& writer;

    void formatDiag(SourceLocation loc, std::span<const SourceRange> ranges,
                    DiagnosticSeverity severity, std::string_view message,
                    std::string_view optionName);
};

} // namespace slang
