//------------------------------------------------------------------------------
//! @file DiagnosticClient.h
//! @brief Client interface for diagnostic rendering
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/util/Util.h"

namespace slang {

class DiagnosticClient {
public:
    virtual ~DiagnosticClient() = default;
    virtual void report(const ReportedDiagnostic& diagnostic) = 0;

    void setEngine(const DiagnosticEngine& engine);

protected:
    const DiagnosticEngine* engine = nullptr;
    const SourceManager* sourceManager = nullptr;

    void getIncludeStack(BufferID buffer, SmallVector<SourceLocation>& stack) const;
    string_view getSourceLine(SourceLocation location, size_t col) const;
    static string_view getSeverityString(DiagnosticSeverity severity);
};

} // namespace slang
