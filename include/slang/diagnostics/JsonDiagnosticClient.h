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

class SLANG_EXPORT JsonDiagnosticClient : public DiagnosticClient {
public:
    JsonDiagnosticClient(JsonWriter& writer) : writer(writer) {}

    void report(const ReportedDiagnostic& diagnostic) override;

private:
    JsonWriter& writer;

    void formatDiag(SourceLocation loc, std::span<const SourceRange> ranges,
                    DiagnosticSeverity severity, std::string_view message,
                    std::string_view optionName);
};

} // namespace slang
