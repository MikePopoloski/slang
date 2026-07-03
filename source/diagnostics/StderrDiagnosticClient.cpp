//------------------------------------------------------------------------------
// StderrDiagnosticClient.cpp
// Diagnostic client that prints output to stderr
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/StderrDiagnosticClient.h"

#include "slang/util/OS.h"

namespace slang {

void StderrDiagnosticClient::report(const ReportedDiagnostic& diagnostic) {
    TextDiagnosticClient::report(diagnostic);
    OS::printE(getString());
    clear();
}

} // namespace slang
