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

/// A base class for diagnostic clients, which receive issued diagnostics
/// and present them to the user in some form.
class SLANG_EXPORT DiagnosticClient {
public:
    virtual ~DiagnosticClient() = default;

    /// Called when a diagnostic is issued by the engine.
    virtual void report(const ReportedDiagnostic& diagnostic) = 0;

    /// Sets the engine that this client is associated with.
    /// This is called by the engine when the client is added to it.
    void setEngine(const DiagnosticEngine& engine);

    /// Sets whether displayed filenames for diagnostics should be
    /// made absolute, or whether to use the relative path.
    void showAbsPaths(bool set) { absPaths = set; }

protected:
    const DiagnosticEngine* engine = nullptr;
    const SourceManager* sourceManager = nullptr;
    bool absPaths = false;

    std::string getFileName(SourceLocation location) const;
    void getIncludeStack(BufferID buffer, SmallVectorBase<SourceLocation>& stack) const;
    std::string_view getSourceLine(SourceLocation location, size_t col) const;
    static std::string_view getSeverityString(DiagnosticSeverity severity);
};

} // namespace slang
