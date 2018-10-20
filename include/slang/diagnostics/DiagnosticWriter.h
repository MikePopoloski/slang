//------------------------------------------------------------------------------
// DiagnosticWriter.h
// Diagnostic rendering.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <unordered_map>

#include "slang/diagnostics/Diagnostics.h"

namespace slang {

class SourceManager;

/// The severity of a given diagnostic. This is not tied to the diagnostic itself;
/// it can be configured on a per-diagnostic basis at runtime.
enum class DiagnosticSeverity { Note, Warning, Error };

class DiagnosticWriter {
public:
    explicit DiagnosticWriter(const SourceManager& sourceManager);

    /// Sets the message to use for the given diagnostic.
    void setMessage(DiagCode code, std::string format);

    /// Sets the severity to use for the given diagnostic.
    void setSeverity(DiagCode code, DiagnosticSeverity severity);

    /// Gets the current severity of the given diagnostic.
    DiagnosticSeverity getSeverity(DiagCode code) const;

    /// Writes a report for the given diagnostic.
    std::string report(const Diagnostic& diagnostic);

    /// Writes a report for all of the diagnostics in the given collection.
    /// Note that this modifies the collection by sorting it.
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

    // Little structure to hold a diagnostic's format and severity.
    struct Descriptor {
        std::string format;
        DiagnosticSeverity severity;
    };

    std::unordered_map<DiagCode, Descriptor> descriptors;
};

} // namespace slang