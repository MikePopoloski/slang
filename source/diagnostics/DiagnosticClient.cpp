//------------------------------------------------------------------------------
// DiagnosticClient.cpp
// Client interface for diagnostic rendering
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticClient.h"

#include "slang/text/SourceManager.h"

namespace slang {

void DiagnosticClient::setEngine(const DiagnosticEngine& newEngine) {
    if (engine && engine != &newEngine)
        SLANG_THROW(std::runtime_error("Diagnostic client already has a different engine set"));

    engine = &newEngine;
    sourceManager = &engine->getSourceManager();
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

std::string_view DiagnosticClient::getSourceLine(SourceLocation location, size_t col) const {
    std::string_view text = sourceManager->getSourceText(location.buffer());
    if (text.empty())
        return "";

    const char* start = text.data() + location.offset() - (col - 1);
    const char* curr = start;
    const char* end = text.data() + text.size() - 1;
    while (curr != end && *curr != '\n' && *curr != '\r')
        curr++;

    return std::string_view(start, (size_t)(curr - start));
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
        default:
            SLANG_UNREACHABLE;
    }
}

} // namespace slang
