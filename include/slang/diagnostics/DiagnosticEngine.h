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

/// The DiagnosticEngine is the central point for controlling how diagnostics are
/// categorized and issued to clients. The clients in this context are in charge of
/// actually reporting diagnostics to the user in whatever format they prefer.
///
/// The workflow here is:
/// - Create a DiagnosticEngine and configure it how you desire
/// - Register one or more DiagnosticClient derived classes with addClient()
/// - Issue diagnostics by calling issue()
///
class DiagnosticEngine {
public:
    /// Constructs a new diagnostic engine, using the specified source manager
    /// for reporting source-based information from diagnostics.
    explicit DiagnosticEngine(const SourceManager& sourceManager);
    ~DiagnosticEngine();

    /// Adds a client which will receive all future diagnostics that are issued.
    void addClient(const std::shared_ptr<DiagnosticClient>& client);

    /// Clears all previously registered clients from the engine.
    void clearClients();

    /// Issues a diagnostic to all registered clients. The issued diagnostic can
    /// be filtered or remapped based on current settings.
    void issue(const Diagnostic& diagnostic);

    /// Gets the source manager associated with the engine.
    const SourceManager& getSourceManager() const { return sourceManager; }

    /// Gets the number of errors and fatal errors issued so far (including all
    /// diagnostics that were remapped to be considered errors).
    int getNumErrors() const { return numErrors; }

    /// Gets the number of warnings issued so far (including all diagnostics that
    /// were remapped to be considered warnings but not including diagnostics that
    /// were remapped to be ignored).
    int getNumWarnings() const { return numWarnings; }

    /// Clears the number of errors and warnings issued, and in addition clears out
    /// the state of which include files for which we've already reported include stacks.
    void clearCounts();

    /// Sets the limit on the number of errors that will be issued (including fatal errors).
    /// Once the limit is reached, the engine will filter all further errors. If the limit
    /// is set to zero (the default) the limit is infinite.
    void setErrorLimit(int limit) { errorLimit = limit; }

    /// Sets whether all warnings should be ignored. Note that this does not apply to
    /// diagnostics that have an overridden severity specified via setSeverity().
    void setIgnoreAllWarnings(bool set) { ignoreAllWarnings = set; }

    /// Sets whether all notes should be ignored. Note that this does not apply to
    /// diagnostics that have an overridden severity specified via setSeverity().
    void setIgnoreAllNotes(bool set) { ignoreAllNotes = set; }

    /// Sets whether all warnings should be treated as errors. Note that this does not
    /// apply to diagnostics that have an overridden severity specified via setSeverity().
    void setWarningsAsErrors(bool set) { warningsAsErrors = set; }

    /// Sets whether all errors should be treated as fatal errors. Note that this does not
    /// apply to diagnostics that have an overridden severity specified via setSeverity().
    /// Also note that if both this and setFatalsAsErrors is set, this one takes precedence.
    void setErrorsAsFatal(bool set) { errorsAsFatal = set; }

    /// Sets whether all fatal errors should be treated as normal errors. Note that this
    /// does not apply to diagnostics that have an overridden severity specified via
    /// setSeverity(). Also note that if both this and setErrorsAsFatal is set, the
    /// other one takes precedence.
    void setFatalsAsErrors(bool set) { fatalsAsErrors = set; }

    /// Gets the set of options currently being used to print type names in diagnostics.
    TypePrintingOptions& typeOptions() { return *typePrintingOptions; }

    /// Gets the set of options currently being used to print type names in diagnostics.
    const TypePrintingOptions& typeOptions() const { return *typePrintingOptions; }

    /// Sets the severity for the given diagnostic. If this is a built-in diagnostic
    /// this will essentially override its default severity. Otherwise this can
    /// be used to define a new user-specified diagnostic.
    void setSeverity(DiagCode code, DiagnosticSeverity severity);

    /// Sets the severity for all of diagnostics in the given group.
    void setSeverity(const DiagGroup& group, DiagnosticSeverity severity);

    /// Gets the severity currently mapped for the given diagnostic.
    DiagnosticSeverity getSeverity(DiagCode code) const;

    /// Sets the message to use for the given diagnostic. If this is a built-in
    /// diagnostic this will essentially override its default message. Otherwise
    /// this can be used to define a new user-specified diagnostic.
    void setMessage(DiagCode code, const std::string& message);

    /// Gets the message currently mapped for the given diagnostic.
    string_view getMessage(DiagCode code) const;

    /// Gets the option string that can be used to refer to a particular diagnostic.
    /// If the diagnostic has no option string provided, this returns an empty string.
    string_view getOptionName(DiagCode code) const;

    /// Finds a diagnostic given an option name. If no matching diagnostic is found,
    /// returns an empty diagnostic code.
    DiagCode findFromOptionName(string_view optionName) const;

    /// Finds the diagnostic group with the given name, if it exists. Otherwise returns nullptr.
    const DiagGroup* findDiagGroup(string_view name) const;

    /// Returns true if the given diagnostic has a custom severity mapping specified
    /// by a previous call to setSeverity(). Otherwise returns false.
    bool hasCustomSeverity(DiagCode code) const;

    /// Clears out all custom mappings for diagnostics, reverting built-ins back to
    /// their defaults and removing all user-specified diagnostics.
    void clearMappings();

    /// Clears out all custom mappings for diagnostics that are set to the specific
    /// severity type.
    void clearMappings(DiagnosticSeverity severity);

    /// Formats the given diagnostic using its arguments and the currently mapped
    /// message for its diagnostic code.
    std::string formatMessage(const Diagnostic& diag) const;

    /// Sets diagnostic options from the given option strings, typically from a list of -W
    /// arguments passed to a command line invocation. Any errors encountered while parsing
    /// the options are returned via the diagnostics set.
    Diagnostics setWarningOptions(span<const std::string> options);

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

    /// A helper method used as a shortcut to turn all of the specified diagnostics into
    /// a human-friendly string. This is mostly intended to be used for things like tests.
    static std::string reportAll(const SourceManager& sourceManager, span<const Diagnostic> diags);

private:
    void issueImpl(const Diagnostic& diagnostic, DiagnosticSeverity severity);

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
    bool issuedOverLimitErr = false;
};

} // namespace slang