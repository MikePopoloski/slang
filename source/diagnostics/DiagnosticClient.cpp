//------------------------------------------------------------------------------
// DiagnosticClient.cpp
// Client interface for diagnostic rendering
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticClient.h"

#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace slang {

void DiagnosticClient::setEngine(const DiagnosticEngine& newEngine) {
    if (engine && engine != &newEngine)
        SLANG_THROW(std::runtime_error("Diagnostic client already has a different engine set"));

    engine = &newEngine;
    sourceManager = &engine->getSourceManager();
}

std::string DiagnosticClient::getFileName(SourceLocation location) const {
    if (absPaths)
        return getU8Str(sourceManager->getFullPath(location.buffer()));
    else
        return std::string(sourceManager->getFileName(location));
}

void DiagnosticClient::getIncludeStack(BufferID buffer,
                                       SmallVectorBase<SourceLocation>& stack) const {
    stack.clear();
    while (buffer) {
        SourceLocation loc = sourceManager->getIncludedFrom(buffer);
        if (!loc.buffer())
            break;

        stack.push_back(loc);
        buffer = loc.buffer();
    }
}

size_t DiagnosticClient::getColumnNumber(SourceLocation location) const {
    return columnUnit == ColumnUnit::Display ? sourceManager->getDisplayColumnNumber(location)
                                             : sourceManager->getColumnNumber(location);
}

std::string_view DiagnosticClient::getSeverityString(DiagnosticSeverity severity) {
    switch (severity) {
        case DiagnosticSeverity::Ignored:
            return "ignored";
        case DiagnosticSeverity::Note:
            return "note";
        case DiagnosticSeverity::Warning:
            return "warning";
        case DiagnosticSeverity::Error:
            return "error";
        case DiagnosticSeverity::Fatal:
            return "fatal error";
    }
    SLANG_UNREACHABLE;
}

} // namespace slang
