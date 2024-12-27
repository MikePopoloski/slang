//------------------------------------------------------------------------------
//! @file DiagnosticEngine.h
//! @brief Primary interface for managing diagnostic reporting
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <functional>
#include <memory>
#include <string>
#include <typeindex>
#include <typeinfo>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/Hash.h"
#include "slang/util/TypeTraits.h"

namespace slang {

namespace ast {
class Symbol;
}

class DiagArgFormatter;
class DiagnosticClient;
class SourceManager;

struct SLANG_EXPORT ReportedDiagnostic {
    const Diagnostic& originalDiagnostic;
    std::span<const SourceLocation> expansionLocs;
    std::span<const SourceRange> ranges;
    SourceLocation location;
    std::string_view formattedMessage;
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
class SLANG_EXPORT DiagnosticEngine {
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

    /// Sets the severity for the given diagnostic. If this is a built-in diagnostic
    /// this will essentially override its default severity. Otherwise this can
    /// be used to define a new user-specified diagnostic.
    void setSeverity(DiagCode code, DiagnosticSeverity severity);

    /// Sets the severity for all of diagnostics in the given group.
    void setSeverity(const DiagGroup& group, DiagnosticSeverity severity);

    /// Gets the severity currently mapped for the given diagnostic, at the given
    /// location in the source code.
    DiagnosticSeverity getSeverity(DiagCode code, SourceLocation location) const;

    /// Sets the message to use for the given diagnostic. If this is a built-in
    /// diagnostic this will essentially override its default message. Otherwise
    /// this can be used to define a new user-specified diagnostic.
    void setMessage(DiagCode code, const std::string& message);

    /// Gets the message currently mapped for the given diagnostic.
    std::string_view getMessage(DiagCode code) const;

    /// Gets the option string that can be used to refer to a particular diagnostic.
    /// If the diagnostic has no option string provided, this returns an empty string.
    std::string_view getOptionName(DiagCode code) const;

    /// Finds a diagnostic given an option name. If no matching diagnostic is found,
    /// returns an empty diagnostic code.
    std::span<const DiagCode> findFromOptionName(std::string_view optionName) const;

    /// Finds the diagnostic group with the given name, if it exists. Otherwise returns nullptr.
    const DiagGroup* findDiagGroup(std::string_view name) const;

    /// Clears out all custom mappings for diagnostics, reverting built-ins back to
    /// their defaults and removing all user-specified diagnostics.
    void clearMappings();

    /// Clears out all custom mappings for diagnostics that are set to the specific
    /// severity type.
    void clearMappings(DiagnosticSeverity severity);

    /// Adds paths for which all warnings will be supressed. This applies to
    /// all natural warnings, regardless of whether they've been upgraded to an error.
    std::error_code addIgnorePaths(std::string_view pattern);

    /// Adds paths for which all warnings will be supressed, when looking at the
    /// original location for macro expansions (i.e. where the macro was originally defined).
    /// This applies to all natural warnings, regardless of whether they've been upgraded
    /// to an error.
    std::error_code addIgnoreMacroPaths(std::string_view pattern);

    /// Sets a custom formatter function for the given type. This is used to
    /// provide formatting for diagnostic arguments of a custom type.
    template<typename ForType>
    void setFormatter(std::shared_ptr<DiagArgFormatter> formatter) {
        formatters[SLANG_TYPEOF(ForType)] = std::move(formatter);
    }

    /// Sets a custom formatter for the given type that should apply by default to
    /// all new DiagnosticEngine instances that get created.
    template<typename ForType>
    static void setDefaultFormatter(std::shared_ptr<DiagArgFormatter> formatter) {
        defaultFormatters[SLANG_TYPEOF(ForType)] = std::move(formatter);
    }

    using SymbolPathCB = std::function<std::string(const ast::Symbol&)>;

    /// Sets a callback that will be used to get a symbol path for a given symbol.
    template<typename TFunc>
    void setSymbolPathCB(TFunc&& func) {
        symbolPathCB = std::forward<TFunc>(func);
    }

    /// Gets the callback to use for getting a symbol path for a given symbol.
    const SymbolPathCB& getSymbolPathCB() const { return symbolPathCB; }

    /// Sets the default callback to use for getting a symbol path for a given symbol,
    /// which will be used if a specific callback is not set on a DiagnosticEngine instance.
    template<typename TFunc>
    static void setDefaultSymbolPathCB(TFunc&& func) {
        defaultSymbolPathCB = std::forward<TFunc>(func);
    }

    /// Formats the given diagnostic using its arguments and the currently mapped
    /// message for its diagnostic code.
    std::string formatMessage(const Diagnostic& diag) const;

    /// Initializes diagnostic warnings to the default group.
    void setDefaultWarnings();

    /// Sets diagnostic options from the given option strings, typically from a list of -W
    /// arguments passed to a command line invocation. Any errors encountered while parsing
    /// the options are returned via the diagnostics set.
    Diagnostics setWarningOptions(std::span<const std::string> options);

    /// Sets diagnostic options from the `pragma diagnostic entries in all of the various
    /// source files tracked by the engine's source manager. Any errors encountered
    /// while applying options are returned via the diagnostics set.
    Diagnostics setMappingsFromPragmas();

    /// Sets diagnostic options from the `pragma diagnostic entries in the given
    /// source file tracked by the engine's source manager. Any errors encountered
    /// while applying options are returned via the diagnostics set.
    Diagnostics setMappingsFromPragmas(BufferID buffer);

    /// A helper function that takes a set of source ranges and translates them
    /// to be relevant to the given context location. For normal file ranges
    /// this doesn't do anything, but ranges within macro expansions get adjusted
    /// to their original expansion location in the same buffer as the context location.
    ///
    /// If @a mapOriginalLocations is set to true, the returned source ranges will
    /// be specified in their original textual locations. Otherwise they will
    /// remain as macro locations.
    void mapSourceRanges(SourceLocation loc, std::span<const SourceRange> ranges,
                         SmallVectorBase<SourceRange>& mapped,
                         bool mapOriginalLocations = true) const;

    /// A helper method used as a shortcut to turn all of the specified diagnostics into
    /// a human-friendly string. This is mostly intended to be used for things like tests.
    static std::string reportAll(const SourceManager& sourceManager,
                                 std::span<const Diagnostic> diags);

private:
    // An entry added by `pragma diagnostic at the given source offset which
    // sets a diagnostic to the given severity.
    struct DiagnosticMapping {
        size_t offset = 0;
        std::optional<DiagnosticSeverity> severity;

        DiagnosticMapping(size_t offset, std::optional<DiagnosticSeverity> severity) noexcept :
            offset(offset), severity(severity) {}
    };

    std::optional<DiagnosticSeverity> findMappedSeverity(DiagCode code,
                                                         SourceLocation location) const;
    bool issueImpl(const Diagnostic& diagnostic, DiagnosticSeverity severity);

    template<typename TDirective>
    void setMappingsFromPragmasImpl(BufferID buffer, std::span<const TDirective> directives,
                                    Diagnostics& diags);

    // The source manager used to resolve locations into file names.
    const SourceManager& sourceManager;

    // Tracking for the number of errors and warnings we've issued.
    int numErrors = 0;
    int numWarnings = 0;

    // Configurable controls for when and how we issue diagnostics.
    int errorLimit = 0;
    bool ignoreAllWarnings = false;
    bool ignoreAllNotes = false;
    bool warningsAsErrors = false;
    bool errorsAsFatal = false;
    bool fatalsAsErrors = false;

    // Tracking for whether we've already issued an error for going over
    // the configured error limit (we only want to do that once).
    bool issuedOverLimitErr = false;

    // A global mapping from diagnostic to a configured severity it should have.
    flat_hash_map<DiagCode, DiagnosticSeverity> severityTable;

    // A global mapping from diagnostic to the message it should display.
    flat_hash_map<DiagCode, std::string> messageTable;

    // A set of buffers for which we have reported an include stack,
    // so that we don't do it more than once.
    flat_hash_set<BufferID> reportedIncludeStack;

    // A map from diagnostic -> source file -> list of in-source diagnostic mappings.
    // These correspond to `pragma diagnostic entries in the source code.
    flat_hash_map<DiagCode, flat_hash_map<BufferID, std::vector<DiagnosticMapping>>> diagMappings;

    // A list of path patterns in which to suppress warnings.
    std::vector<std::filesystem::path> ignoreWarnPatterns;
    std::vector<std::filesystem::path> ignoreMacroWarnPatterns;

    // A list of all registered clients that receive issued diagnostics.
    std::vector<std::shared_ptr<DiagnosticClient>> clients;

    // Callbacks for retrieving a path for symbol arguments in diagnostics.
    SymbolPathCB symbolPathCB;
    static SymbolPathCB defaultSymbolPathCB;

    // A map from type_index to a formatter for that type. Used to register custom
    // formatters for subsystem-specific types.
    using FormatterMap = flat_hash_map<SLANG_TYPEINDEX, std::shared_ptr<DiagArgFormatter>>;
    mutable FormatterMap formatters;

    // A set of default formatters that will be assigned to each new DiagnosticEngine instance
    // that gets created. These can later be overridden on a per-instance basis.
    static FormatterMap defaultFormatters;
};

} // namespace slang
