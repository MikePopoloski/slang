//------------------------------------------------------------------------------
// DiagnosticWriter.h
// Diagnostic rendering.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <deque>

#include "slang/diagnostics/Diagnostics.h"

namespace slang {

class SourceManager;

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
enum class DiagnosticSeverity { Note, Warning, Error };

class DiagnosticWriter {
public:
    explicit DiagnosticWriter(const SourceManager& sourceManager);

    /// Writes a report for the given diagnostic.
    std::string report(const Diagnostic& diagnostic);

    /// Writes a report for all of the diagnostics in the given collection.
    std::string report(const Diagnostics& diagnostics);

private:
    string_view getBufferLine(SourceLocation location, uint32_t col);
    void getIncludeStack(BufferID buffer, std::deque<SourceLocation>& stack);
    void highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col,
                        string_view sourceLine, std::string& buffer);

    template<typename T>
    void formatDiag(T& buffer, SourceLocation loc, span<const SourceRange> ranges,
                    const char* severity, const std::string& msg);

    const SourceManager& sourceManager;
};

} // namespace slang