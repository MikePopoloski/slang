//------------------------------------------------------------------------------
//! @file Driver.h
//! @brief Driver class with reporting and output functionality for CLI tools.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/BaseDriver.h"

namespace slang {
class JsonDiagnosticClient;
class JsonWriter;
class TextDiagnosticClient;
} // namespace slang

namespace slang::driver {

/// @brief Driver class with reporting and output methods for command-line tools.
///
/// This class extends BaseDriver with methods for various types of output including
/// preprocessor output, macro reporting, and diagnostic reporting.
///
/// A typical compilation flow using the driver looks as follows:
///
/// @code{.cpp}
/// Driver driver;
/// driver.addStandardArgs();
/// if (!driver.parseCommandLine(someStr)) { ...error }
/// if (!driver.processOptions()) { ...error }
/// if (!driver.parseAllSources()) { ...error }
/// if (!driver.runFullCompilation()) { ...error }
/// else { ...success }
/// @endcode
///
class SLANG_EXPORT Driver : public ClientOwningDriver<TextDiagnosticClient> {
public:
    /// Options for configuring diagnostic output formatting.
    struct SLANG_EXPORT DiagnosticFormatOptions {
        /// If true, print diagnostics with color.
        std::optional<bool> colorDiags;

        /// If true, include column numbers in printed diagnostics.
        std::optional<bool> diagColumn;

        /// The unit to use for column numbers in diagnostic output.
        std::optional<ColumnUnit> diagColumnUnit;

        /// If true, include location information in printed diagnostics.
        std::optional<bool> diagLocation;

        /// If true, include source line context in printed diagnostics.
        std::optional<bool> diagSourceLine;

        /// If true, include warning option names in printed diagnostics.
        std::optional<bool> diagOptionName;

        /// If true, include file include stacks in printed diagnostics.
        std::optional<bool> diagIncludeStack;

        /// If true, include macro expansion information in printed diagnostics.
        std::optional<bool> diagMacroExpansion;

        /// If true, display absolute paths to files in printed diagnostics.
        std::optional<bool> diagAbsPaths;

        /// Controls whether to include hierarchy paths in printed diagnostics.
        std::optional<ShowHierarchyPathOption> diagHierarchy;

        /// If set, the path to a JSON file that will be written with diagnostic information.
        /// Can be '-' to indicate that the JSON should be written to stdout.
        std::optional<std::string> diagJson;
    };

    /// Options for configuring dependency file generation.
    struct SLANG_EXPORT DepFileOptions {
        /// Optional target name to include when writing dependency files.
        std::optional<std::string> depfileTarget;

        /// If true, trim unreferenced files before generating dependency lists.
        std::optional<bool> depfileTrim;

        /// If true, topologically sort files before generating dependency lists.
        std::optional<bool> depfileSort;

        /// Output path for a dependency file containing all dependencies.
        std::optional<std::string> allDepfile;

        /// Output path for a dependency file containing include file dependencies.
        std::optional<std::string> includeDepfile;

        /// Output path for a dependency file containing module source file dependencies.
        std::optional<std::string> moduleDepfile;
    };

    /// Options for diagnostic output formatting.
    DiagnosticFormatOptions diagFormatOptions;

    /// Options for dependency file generation.
    DepFileOptions depFileOptions;

    /// The text diagnostics client that will be used to render diagnostics.
    std::shared_ptr<TextDiagnosticClient> textDiagClient;

    /// The (optional) JSON diagnostics client that will be used to render diagnostics.
    std::shared_ptr<JsonDiagnosticClient> jsonDiagClient;

    /// Constructs a new instance of the @a Driver class.
    Driver();
    ~Driver();

    /// @brief Adds standard command line arguments, including diagnostic formatting options.
    ///
    /// This calls the base class method and adds additional diagnostic-related arguments.
    void addStandardArgs();

    /// @brief Processes and applies all configured options, including diagnostic client setup.
    ///
    /// This calls the base class method and adds diagnostic client configuration.
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool processOptions();

    /// @brief Runs the preprocessor on all loaded buffers and outputs the result to stdout.
    ///
    /// Any errors encountered will be printed to stderr.
    /// @param includeComments If true, comments will be included in the output.
    /// @param includeDirectives If true, preprocessor directives will be included in the output.
    /// @param obfuscateIds If true, identifiers will be obfuscated by replacing them with
    ///                     randomized alphanumeric strings.
    /// @param useFixedObfuscationSeed If true, obfuscated identifiers will be generated with
    ///                                a fixed randomization seed, meaning they will be the
    ///                                same every time the program is run. Used for testing.
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool runPreprocessor(bool includeComments, bool includeDirectives,
                                       bool obfuscateIds, bool useFixedObfuscationSeed = false);

    /// Prints all macros from all loaded buffers to stdout.
    void reportMacros();

    /// Writes any dependency files that have been requested via command line options.
    /// (if such options have not been specified this method does nothing).
    void optionallyWriteDepFiles();

    /// @brief Reports all parsing diagnostics found in all of the @a syntaxTrees
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool reportParseDiags();

    /// @brief Reports the result of compilation.
    ///
    /// If @a quiet is set to true, non-essential output will be suppressed.
    void reportCompilation(ast::Compilation& compilation, bool quiet);

    /// @brief Reports all diagnostics to output.
    ///
    /// If @a quiet is set to true, non-essential output will be suppressed.
    /// @returns true if compilation succeeded and false if errors were encountered.
    [[nodiscard]] bool reportDiagnostics(bool quiet);

    /// @brief Runs a full compilation pass and reports the results.
    ///
    /// This is a helper method that calls @a createCompilation, @a reportCompilation,
    /// @a runAnalysis, and @a reportDiagnostics in sequence.
    ///
    /// @returns true if compilation succeeded and false if errors were encountered.
    [[nodiscard]] bool runFullCompilation(bool quiet = false);

private:
    std::unique_ptr<JsonWriter> jsonWriter;
};

} // namespace slang::driver
