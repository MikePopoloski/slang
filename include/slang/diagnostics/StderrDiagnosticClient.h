//------------------------------------------------------------------------------
//! @file StderrDiagnosticClient.h
//! @brief Diagnostic client that prints output to stderr
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/TextDiagnosticClient.h"

namespace slang {

/// A diagnostic client that serializes diagnostics to stderr.
class SLANG_EXPORT StderrDiagnosticClient : public TextDiagnosticClient {
public:
    /// Called by the DiagnosticEngine to report a new diagnostic.
    void report(const ReportedDiagnostic& diagnostic) override;
};

} // namespace slang
