//------------------------------------------------------------------------------
//! @file DiagnosticClient.h
//! @brief Client interface for diagnostic rendering
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/util/Util.h"

namespace slang {

class SLANG_EXPORT DiagnosticClient {
public:
    virtual ~DiagnosticClient() = default;
    virtual void report(const ReportedDiagnostic& diagnostic) = 0;

    void setEngine(const DiagnosticEngine& engine);

protected:
    const DiagnosticEngine* engine = nullptr;
    const SourceManager* sourceManager = nullptr;

    void getIncludeStack(BufferID buffer, SmallVectorBase<SourceLocation>& stack) const;
    std::string_view getSourceLine(SourceLocation location, size_t col) const;
    static std::string_view getSeverityString(DiagnosticSeverity severity);
};

} // namespace slang
