//------------------------------------------------------------------------------
//! @file Driver.h
//! @brief Top-level handler for processing arguments and
//! constructing a compilation for a CLI tool.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/text/SourceManager.h"
#include "slang/util/CommandLine.h"
#include "slang/util/OS.h"
#include "slang/util/Util.h"

namespace slang {

class TextDiagnosticClient;

namespace syntax {
class SyntaxTree;
}

} // namespace slang

namespace slang::driver {

/// A top-level class that handles argument parsing, option preparation,
/// and invoking various parts of the slang compilation process.
/// This is exposed as a convenience wrapper around the various components
/// that could otherwise be used on their own.
class SLANG_EXPORT Driver {
public:
    /// The command line object that will be used to parse
    /// arguments if the @a parseCommandLine method is called.
    CommandLine cmdLine;

    /// The source manager that holds all loaded source files.
    SourceManager sourceManager;

    /// The diagnostics engine that will be used to report diagnostics.
    DiagnosticEngine diagEngine;

    /// The diagnostics client that will be used to render diagnostics.
    std::shared_ptr<TextDiagnosticClient> diagClient;

    /// A list of source buffers that have been loaded.
    std::vector<SourceBuffer> buffers;

    /// A list of syntax trees that have been parsed.
    std::vector<std::shared_ptr<syntax::SyntaxTree>> syntaxTrees;

    /// A container for various options that can be parsed and applied
    /// to the compilation process.
    struct Options {
        /// @name Include paths
        /// @{

        /// A list of include directories in which to search for files.
        std::vector<std::string> includeDirs;

        /// A list of system include directories in which to search for files.
        std::vector<std::string> includeSystemDirs;

        /// A list of library directories in which to search for missing modules.
        std::vector<std::string> libDirs;

        /// A list of extensions that will be used to search for library files.
        std::vector<std::string> libExts;

        /// A set of extensions that will be used to exclude files.
        flat_hash_set<std::string> excludeExts;

        /// A set of preprocessor directives to be ignored.
        std::vector<std::string> ignoreDirectives;

        /// @}
        /// @name Preprocessing
        /// @{

        /// The maximum depth of included files before an error is issued.
        std::optional<uint32_t> maxIncludeDepth;

        /// A list of macros that should be defined in each compilation unit.
        std::vector<std::string> defines;

        /// A list of macros that should be undefined in each compilation unit.
        std::vector<std::string> undefines;

        /// If true, library files will inherit macro definitions from primary source files.
        std::optional<bool> librariesInheritMacros;

        /// @}
        /// @name Parsing
        /// @{

        /// The maximum call stack depth of parsing before an error is issued.
        std::optional<uint32_t> maxParseDepth;

        /// The maximum number of lexer errors that can be encountered before giving up.
        std::optional<uint32_t> maxLexerErrors;

        /// @}
        /// @name Compilation
        /// @{

        /// The maximum depth of nested module instances (and interfaces/programs),
        /// to detect infinite recursion.
        std::optional<uint32_t> maxInstanceDepth;

        /// The maximum number of steps that will be taken when expanding a single
        /// generate construct, to detect infinite loops.
        std::optional<uint32_t> maxGenerateSteps;

        /// The maximum depth of nested function calls in constant expressions,
        /// to detect infinite recursion.
        std::optional<uint32_t> maxConstexprDepth;

        /// The maximum number of steps to allow when evaluating a constant expressions,
        /// to detect infinite loops.
        std::optional<uint32_t> maxConstexprSteps;

        /// The maximum number of frames in a callstack to display in diagnostics
        /// before abbreviating them.
        std::optional<uint32_t> maxConstexprBacktrace;

        /// The maximum number of instances allowed in a single instance array.
        std::optional<uint32_t> maxInstanceArray;

        /// A string indicating a member of @a CompatMode to use for tailoring
        /// other compilation options.
        std::optional<std::string> compat;

        /// A string indicating a member of @a MinTypMax to indicate which set
        /// of (min:typ:max) expressions is valid for this compilation.
        std::optional<std::string> minTypMax;

        /// A string that indicates the default time scale to use for
        /// any design elements that don't specify one explicitly.
        std::optional<std::string> timeScale;

        /// If true, allow various to be referenced before they are declared.
        std::optional<bool> allowUseBeforeDeclare;

        /// If true, ignore errors about unknown modules.
        std::optional<bool> ignoreUnknownModules;

        /// If true, allow all integral types to convert implicitly to enum types.
        std::optional<bool> relaxEnumConversions;

        /// If true, allow hierarchical names in constant expressions.
        std::optional<bool> allowHierarchicalConst;

        /// Signals driven by an always_comb are normally not allowed to be driven
        /// by any other process. Setting this option allows initial blocks to
        /// also drive such signals.
        std::optional<bool> allowDupInitialDrivers;

        /// If true, perform strict checking of variable drivers, which currently
        /// means not taking into account procedural for loop unrolling.
        std::optional<bool> strictDriverChecking;

        /// If true, only perform linting of code, don't try to elaborate a full hierarchy.
        std::optional<bool> onlyLint;

        /// If non-empty, specifies the list of modules that should serve as the
        /// top modules in the design. If empty, this will be automatically determined
        /// based on which modules are unreferenced elsewhere.
        std::vector<std::string> topModules;

        /// A list of parameters to override, of the form &lt;name>=&lt;value> -- note that
        /// for now at least this only applies to parameters in top-level modules.
        std::vector<std::string> paramOverrides;

        /// @}
        /// @name Diagnostics control
        /// @{

        /// If true, print diagnostics with color.
        std::optional<bool> colorDiags;

        /// If true, include column numbers in printed diagnostics.
        std::optional<bool> diagColumn;

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

        /// If true, include hierarchy paths in printed diagnostics.
        std::optional<bool> diagHierarchy;

        /// The maximum number of errors to print before giving up.
        std::optional<uint32_t> errorLimit;

        /// A list of warning options that will be passed to the DiagnosticEngine.
        std::vector<std::string> warningOptions;

        /// A list of paths in which to suppress warnings.
        std::vector<std::string> suppressWarningsPaths;

        /// @}
        /// @name File lists
        /// @{

        /// If set to true, all source files will be treated as part of a single
        /// compilation unit, meaning all of their text will be merged together.
        std::optional<bool> singleUnit;

        /// A list of library files to include in the compilation.
        std::vector<std::string> libraryFiles;

        /// @}
    } options;

    /// Constructs a new instance of the @a Driver class.
    Driver();

    /// Adds standard command line arguments to the @a cmdLine object.
    /// If not called, no arguments will be added by default, though the user
    /// can still add their own custom arguments if desired.
    void addStandardArgs();

    /// Parses command line arguments from the given C-style argument list.
    /// This is templated to support both char and wchar_t arg lists.
    /// Any errors encountered will be printed to stderr.
    template<typename TArgs>
    [[nodiscard]] bool parseCommandLine(int argc, TArgs argv) {
        if (!cmdLine.parse(argc, argv)) {
            for (auto& err : cmdLine.getErrors())
                OS::printE(err + '\n');
            return false;
        }
        return !anyFailedLoads;
    }

    /// Parses command line arguments from the given string.
    /// Any errors encountered will be printed to stderr.
    [[nodiscard]] bool parseCommandLine(string_view argList);

    /// Reads a source file into the SourceManager and returns the buffer handle for it.
    /// If an error occurs a diagnostic will be issued to stderr.
    SourceBuffer readSource(string_view fileName);

    /// Processes the given command file for more options.
    /// Any errors encountered will be printed to stderr.
    /// @param fileName The name (and potentially the path) of the command file to process.
    /// @param makeRelative indicates whether paths in the file are relative to the file
    ///                     itself or to the current working directory.
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool processCommandFile(string_view fileName, bool makeRelative);

    /// Processes and applies all configured options.
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool processOptions();

    /// Runs the preprocessor on all loaded buffers and outputs the result to stdout.
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

    /// Parses all loaded buffers into syntax trees and appends the resulting trees
    /// to the @a syntaxTrees list.
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool parseAllSources();

    /// Creates an options bag from all of the currently set options.
    [[nodiscard]] Bag createOptionBag() const;

    /// Creates a compilation object from all of the current loaded state of the driver.
    [[nodiscard]] std::unique_ptr<ast::Compilation> createCompilation() const;

    /// Reports all parsing diagnostics found in all of the @a syntaxTrees
    /// @returns true on success and false if errors were encountered.
    [[nodiscard]] bool reportParseDiags();

    /// Reports the result of compilation.
    /// If @a quiet is set to true, non-essential output will be suppressed.
    /// @returns true if compilation succeeded and false if errors were encountered.
    [[nodiscard]] bool reportCompilation(ast::Compilation& compilation, bool quiet);

private:
    bool anyFailedLoads = false;
};

} // namespace slang::driver
