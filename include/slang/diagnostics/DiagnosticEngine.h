//------------------------------------------------------------------------------
// DiagnosticEngine.h
// Primary interface for managing diagnostic reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <memory>
#include <string>

#include "slang/diagnostics/Diagnostics.h"

namespace slang {

class DiagnosticClient;
class SourceManager;
struct TypePrintingOptions;

struct ReportedDiagnostic {
    const Diagnostic& originalDiagnostic;
    span<const SourceLocation> expansionLocs;
    span<const SourceRange> ranges;
    SourceLocation location;
    string_view formattedMessage;
    DiagnosticSeverity severity = DiagnosticSeverity::Ignored;
    bool shouldShowIncludeStack = false;

    ReportedDiagnostic(const Diagnostic& original) : originalDiagnostic(original) {}
};

class DiagnosticEngine {
public:
    explicit DiagnosticEngine(const SourceManager& sourceManager);
    ~DiagnosticEngine();

    void addClient(const std::shared_ptr<DiagnosticClient>& client);
    void clearClients();

    void issue(const Diagnostic& diagnostic);

    const SourceManager& getSourceManager() const { return sourceManager; }

    int getNumErrors() const { return numErrors; }
    int getNumWarnings() const { return numWarnings; }

    void clearCounts();

    void setErrorLimit(int limit) { errorLimit = limit; }

    void setIgnoreAllWarnings(bool set) { ignoreAllWarnings = set; }

    void setIgnoreAllNotes(bool set) { ignoreAllNotes = set; }

    void setWarningsAsErrors(bool set) { warningsAsErrors = set; }

    void setErrorsAsFatal(bool set) { errorsAsFatal = set; }

    void setFatalsAsErrors(bool set) { fatalsAsErrors = set; }

    TypePrintingOptions& typeOptions() { return *typePrintingOptions; }
    const TypePrintingOptions& typeOptions() const { return *typePrintingOptions; }

    void setSeverity(DiagCode code, DiagnosticSeverity severity);
    DiagnosticSeverity getSeverity(DiagCode code) const;

    void setMessage(DiagCode code, const std::string& message);
    string_view getMessage(DiagCode code) const;

    void clearMappings();

    std::string formatMessage(const Diagnostic& diag) const;

    /// A helper function that takes a set of source ranges and translates them
    /// to be relevant to the given context location. For normal file ranges
    /// this doesn't do anything, but ranges within macro expansions get adjusted
    /// to their original expansion location in the same buffer as the context location.
    ///
    /// If @a mapOriginalLocations is set to true, the returned source ranges will
    /// be specified in their original textual locations. Otherwise they will
    /// remain as macro locations.
    void mapSourceRanges(SourceLocation loc, span<const SourceRange> ranges,
                         SmallVector<SourceRange>& mapped, bool mapOriginalLocations = true) const;

    static std::string reportAll(const SourceManager& sourceManager, span<const Diagnostic> diags);

private:
    const SourceManager& sourceManager;
    std::unique_ptr<TypePrintingOptions> typePrintingOptions;
    flat_hash_map<DiagCode, DiagnosticSeverity> severityTable;
    flat_hash_map<DiagCode, std::string> messageTable;
    flat_hash_set<BufferID> reportedIncludeStack;
    std::vector<std::shared_ptr<DiagnosticClient>> clients;
    int numErrors = 0;
    int numWarnings = 0;
    int errorLimit = 0;
    bool ignoreAllWarnings = false;
    bool ignoreAllNotes = false;
    bool warningsAsErrors = false;
    bool errorsAsFatal = false;
    bool fatalsAsErrors = false;
};

} // namespace slang