//------------------------------------------------------------------------------
// Driver.cpp
// Top-level handler for processing arguments and
// constructing a compilation for a CLI tool.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/Driver.h"

#include <fmt/color.h>

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/JsonDiagnosticClient.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/SourceLoader.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/Json.h"
#include "slang/util/Random.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace ast;
using namespace parsing;
using namespace syntax;
using namespace analysis;

// clang-format off
#define VCS_COMP_FLAGS \
    CompilationFlags::AllowHierarchicalConst, \
    CompilationFlags::RelaxEnumConversions, \
    CompilationFlags::AllowUseBeforeDeclare, \
    CompilationFlags::RelaxStringConversions, \
    CompilationFlags::AllowRecursiveImplicitCall, \
    CompilationFlags::AllowBareValParamAssignment, \
    CompilationFlags::AllowSelfDeterminedStreamConcat, \
    CompilationFlags::AllowMergingAnsiPorts

static constexpr auto vcsCompFlags = {VCS_COMP_FLAGS};
static constexpr auto allCompFlags = {
    VCS_COMP_FLAGS,
    CompilationFlags::AllowTopLevelIfacePorts,
    CompilationFlags::AllowUnnamedGenerate,
    CompilationFlags::AllowVirtualIfaceWithOverride
};

#define VCS_ANALYSIS_FLAGS \
    AnalysisFlags::AllowMultiDrivenLocals

static constexpr auto vcsAnalysisFlags = {VCS_ANALYSIS_FLAGS};
static constexpr auto allAnalysisFlags = {
    VCS_ANALYSIS_FLAGS,
    AnalysisFlags::AllowDupInitialDrivers
};
// clang-format on

Driver::Driver() : diagEngine(sourceManager), sourceLoader(sourceManager) {
    textDiagClient = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(textDiagClient);
}

Driver::~Driver() = default;

void Driver::addStandardArgs() {
    cmdLine.add("--std", options.languageVersion,
                "The version of the Verilog or SystemVerilog language to use",
                "(1364-2005 | 1800-2017 | 1800-2023 | latest)");

    // Include paths
    cmdLine.add(
        "-I,--include-directory,+incdir",
        [this](std::string_view value) {
            if (auto ec = sourceManager.addUserDirectories(value)) {
                printWarning(fmt::format("include directory '{}': {}", value, ec.message()));
            }
            return "";
        },
        "Additional include search paths", "<dir-pattern>[,...]", CommandLineFlags::CommaList);

    cmdLine.add(
        "--isystem",
        [this](std::string_view value) {
            if (auto ec = sourceManager.addSystemDirectories(value)) {
                printWarning(fmt::format("system include directory '{}': {}", value, ec.message()));
            }
            return "";
        },
        "Additional system include search paths", "<dir-pattern>[,...]",
        CommandLineFlags::CommaList);

    cmdLine.add("--disable-local-includes", options.disableLocalIncludes,
                "Disables \"local\" include path lookup, where include directives search "
                "relative to the file containing the directive first");

    // Preprocessor
    cmdLine.add("-D,--define-macro,+define", options.defines,
                "Define <macro> to <value> (or 1 if <value> ommitted) in all source files",
                "<macro>=<value>");
    cmdLine.add("-U,--undefine-macro", options.undefines,
                "Undefine macro name at the start of all source files", "<macro>",
                CommandLineFlags::CommaList);
    cmdLine.add("--max-include-depth", options.maxIncludeDepth,
                "Maximum depth of nested include files allowed", "<depth>");
    cmdLine.add("--libraries-inherit-macros", options.librariesInheritMacros,
                "If true, library files will inherit macro definitions from the primary source "
                "files. --single-unit must also be passed when this option is used.");
    cmdLine.add("--enable-legacy-protect", options.enableLegacyProtect,
                "If true, the preprocessor will support legacy protected envelope directives, "
                "for compatibility with old Verilog tools");
    cmdLine.add("--translate-off-format", options.translateOffOptions,
                "Set a format for comment directives that mark a region of disabled "
                "source text. The format is a common keyword, a start word, and an "
                "end word, each separated by commas. For example, "
                "'pragma,translate_off,translate_on'",
                "<common>,<start>,<end>");
    cmdLine.add(
        "--map-keyword-version",
        [this](std::string_view value) { return parseMapKeywordVersion(value); },
        "Indicates that any files used during parsing which match the given patterns should "
        "be parsed using the provided language keywords version, as if they contained a "
        "`begin_keywords directive. For example '1364-2005+*.v,*.vh'",
        "<keyword-version>+<file-pattern>[,...]. ");

    // Legacy vendor commands support
    cmdLine.add(
        "--cmd-ignore", [this](std::string_view value) { return cmdLine.addIgnoreCommand(value); },
        "Define rule to ignore vendor command <vendor_cmd> with its following <N> parameters.\n"
        "A command of the form +xyz will also match any vendor command of the form +xyz+abc,\n"
        "as +abc is the command's argument, and doesn't need to be matched.",
        "<vendor_cmd>,<N>");
    cmdLine.add(
        "--cmd-rename", [this](std::string_view value) { return cmdLine.addRenameCommand(value); },
        "Define rule to rename vendor command <vendor_cmd> into existing <slang_cmd>",
        "<vendor_cmd>,<slang_cmd>");
    cmdLine.add("--ignore-directive", options.ignoreDirectives,
                "Ignore preprocessor directive and all its arguments until EOL", "<directive>",
                CommandLineFlags::CommaList);

    // Parsing
    cmdLine.add("--max-parse-depth", options.maxParseDepth,
                "Maximum depth of nested language constructs allowed", "<depth>");
    cmdLine.add("--max-lexer-errors", options.maxLexerErrors,
                "Maximum number of errors that can occur during lexing before the rest of the file "
                "is skipped",
                "<count>");
#if defined(SLANG_USE_THREADS)
    cmdLine.add("-j,--threads", options.numThreads,
                "The number of threads to use to parallelize parsing", "<count>");
#else
    options.numThreads = 1;
#endif

    cmdLine.add(
        "-C",
        [this](std::string_view value) {
            processCommandFiles(value, /* makeRelative */ true, /* separateUnit */ true);
            return "";
        },
        "One or more files containing independent compilation unit listings. "
        "The files accept a subset of options that pertain specifically to parsing "
        "that unit and optionally including it in a library.",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    // Compilation
    cmdLine.add("--max-hierarchy-depth", options.maxInstanceDepth,
                "Maximum depth of the design hierarchy", "<depth>");
    cmdLine.add("--max-generate-steps", options.maxGenerateSteps,
                "Maximum number of steps that can occur during generate block "
                "evaluation before giving up",
                "<steps>");
    cmdLine.add("--max-constexpr-depth", options.maxConstexprDepth,
                "Maximum depth of a constant evaluation call stack", "<depth>");
    cmdLine.add("--max-constexpr-steps", options.maxConstexprSteps,
                "Maximum number of steps that can occur during constant "
                "evaluation before giving up",
                "<steps>");
    cmdLine.add("--constexpr-backtrace-limit", options.maxConstexprBacktrace,
                "Maximum number of frames to show when printing a constant evaluation "
                "backtrace; the rest will be abbreviated",
                "<limit>");
    cmdLine.add("--max-instance-array", options.maxInstanceArray,
                "Maximum number of instances allowed in a single instance array", "<limit>");
    cmdLine.add("--max-enum-values", options.maxEnumValues,
                "Maximum number of members allowed in a single enum declaration", "<limit>");
    cmdLine.add("--max-udp-coverage-notes", options.maxUDPCoverageNotes,
                "Maximum number of UDP coverage notes that will be generated for a single "
                "warning about missing edge transitions",
                "<limit>");
    cmdLine.addEnum<CompatMode, CompatMode_traits>(
        "--compat", options.compat, "Attempt to increase compatibility with the specified tool",
        "<mode>");
    cmdLine.addEnum<MinTypMax, MinTypMax_traits>(
        "-T,--timing", options.minTypMax,
        "Select which value to consider in min:typ:max expressions", "min|typ|max");
    cmdLine.add("--timescale", options.timeScale,
                "Default time scale to use for design elements that don't specify one explicitly",
                "<base>/<precision>");

    auto addCompFlag = [&](CompilationFlags flag, std::string_view name, std::string_view desc) {
        auto [it, inserted] = options.compilationFlags.emplace(flag, std::nullopt);
        SLANG_ASSERT(inserted);
        cmdLine.add(name, it->second, desc);
    };

    addCompFlag(CompilationFlags::AllowUseBeforeDeclare, "--allow-use-before-declare",
                "Don't issue an error for use of names before their declarations");
    addCompFlag(CompilationFlags::IgnoreUnknownModules, "--ignore-unknown-modules",
                "Don't issue an error for instantiations of unknown modules, "
                "interface, and programs");
    addCompFlag(CompilationFlags::RelaxEnumConversions, "--relax-enum-conversions",
                "Allow all integral types to convert implicitly to enum types");
    addCompFlag(CompilationFlags::RelaxStringConversions, "--relax-string-conversions",
                "Allow string types to convert implicitly to integral types");
    addCompFlag(CompilationFlags::AllowHierarchicalConst, "--allow-hierarchical-const",
                "Allow hierarchical references in constant expressions");
    addCompFlag(CompilationFlags::AllowTopLevelIfacePorts, "--allow-toplevel-iface-ports",
                "Allow top-level modules to have interface ports");
    addCompFlag(CompilationFlags::AllowRecursiveImplicitCall, "--allow-recursive-implicit-call",
                "Allow implicit call expressions to be recursive function calls");
    addCompFlag(CompilationFlags::AllowBareValParamAssignment, "--allow-bare-value-param-assigment",
                "Allow module parameter assignments to elide the parentheses");
    addCompFlag(CompilationFlags::AllowSelfDeterminedStreamConcat,
                "--allow-self-determined-stream-concat",
                "Allow self-determined streaming concatenation expressions");
    addCompFlag(CompilationFlags::AllowMergingAnsiPorts, "--allow-merging-ansi-ports",
                "Allow merging ANSI port declarations with nets and variables declared in the "
                "instance body");
    addCompFlag(CompilationFlags::LintMode, "--lint-only",
                "Only perform linting of code, don't try to elaborate a full hierarchy");
    addCompFlag(CompilationFlags::DisableInstanceCaching, "--disable-instance-caching",
                "Disable the use of instance caching, which normally allows skipping duplicate "
                "instance bodies to save time when elaborating");
    addCompFlag(CompilationFlags::DisallowRefsToUnknownInstances,
                "--disallow-refs-to-unknown-instances",
                "When using --ignore-unknown-modules, explicitly disallow references to ignored "
                "module instances by issuing an error");
    addCompFlag(CompilationFlags::AllowUnnamedGenerate, "--allow-genblk-reference",
                "Allow references to unnamed generate blocks via their external names "
                "(e.g. genblk1)");
    addCompFlag(CompilationFlags::AllowVirtualIfaceWithOverride,
                "--allow-virtual-iface-with-override",
                "Allow interface instances that are bind/defparam targets to be assigned "
                "to virtual interfaces");

    cmdLine.add("--top", options.topModules,
                "One or more top-level modules to instantiate "
                "(instead of figuring it out automatically)",
                "<name>", CommandLineFlags::CommaList);
    cmdLine.add("-G", options.paramOverrides,
                "One or more parameter overrides to apply when instantiating top-level modules",
                "<name>=<value>");
    cmdLine.add("-L", options.libraryOrder,
                "A list of library names that controls the priority order for module lookup",
                "<library>", CommandLineFlags::CommaList);
    cmdLine.add("--defaultLibName", options.defaultLibName, "Sets the name of the default library",
                "<name>");

    // Diagnostics control
    cmdLine.add("-W", options.warningOptions, "Control the specified warning", "<warning>");
    cmdLine.add("--color-diagnostics", options.colorDiags,
                "Always print diagnostics in color. "
                "If this option is unset, colors will be enabled if a color-capable "
                "terminal is detected.");
    cmdLine.add("--diag-column", options.diagColumn, "Show column numbers in diagnostic output");
    cmdLine.addEnum<ColumnUnit, ColumnUnit_traits>("--diag-column-unit", options.diagColumnUnit,
                                                   "Unit for column numbers in diagnostics",
                                                   "<unit>");
    cmdLine.add("--diag-location", options.diagLocation,
                "Show location information in diagnostic output");
    cmdLine.add("--diag-source", options.diagSourceLine,
                "Show source line or caret info in diagnostic output");
    cmdLine.add("--diag-option", options.diagOptionName, "Show option names in diagnostic output");
    cmdLine.add("--diag-include-stack", options.diagIncludeStack,
                "Show include stacks in diagnostic output");
    cmdLine.add("--diag-macro-expansion", options.diagMacroExpansion,
                "Show macro expansion backtraces in diagnostic output");
    cmdLine.add("--diag-abs-paths", options.diagAbsPaths,
                "Display absolute paths to files in diagnostic output");
    cmdLine.addEnum<ShowHierarchyPathOption, ShowHierarchyPathOption_traits>(
        "--diag-hierarchy", options.diagHierarchy, "Show hierarchy locations in diagnostic output",
        "always|never|auto");
    cmdLine.add("--diag-json", options.diagJson,
                "Dump all diagnostics in JSON format to the specified file, or '-' for stdout",
                "<file>", CommandLineFlags::FilePath);
    cmdLine.add("--error-limit", options.errorLimit,
                "Limit on the number of errors that will be printed. Setting this to zero will "
                "disable the limit.",
                "<limit>");

    cmdLine.add(
        "--suppress-warnings",
        [this](std::string_view value) {
            if (auto ec = diagEngine.addIgnorePaths(value))
                printWarning(fmt::format("--suppress-warnings path '{}': {}", value, ec.message()));
            return "";
        },
        "One or more paths in which to suppress warnings", "<file-pattern>[,...]",
        CommandLineFlags::CommaList);

    cmdLine.add(
        "--suppress-macro-warnings",
        [this](std::string_view value) {
            if (auto ec = diagEngine.addIgnoreMacroPaths(value)) {
                printWarning(
                    fmt::format("--suppress-macro-warnings path '{}': {}", value, ec.message()));
            }
            return "";
        },
        "One or more paths in which to suppress warnings that "
        "originate in macro expansions",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    // File lists
    cmdLine.add("--single-unit", options.singleUnit,
                "Treat all input files as a single compilation unit");

    cmdLine.add(
        "-v,--libfile",
        [this](std::string_view value) {
            addLibraryFiles(value);
            return "";
        },
        "One or more library files, which are separate compilation units "
        "where modules are not automatically instantiated",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    cmdLine.add(
        "--libmap",
        [this](std::string_view value) {
            sourceLoader.addLibraryMaps(value, {}, createParseOptionBag());
            return "";
        },
        "One or more library map files to parse "
        "for library name mappings and file lists",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    cmdLine.add(
        "-y,--libdir",
        [this](std::string_view value) {
            sourceLoader.addSearchDirectories(value);
            return "";
        },
        "Library search paths, which will be searched for missing modules", "<dir-pattern>[,...]",
        CommandLineFlags::CommaList);

    cmdLine.add(
        "--dir-prefix",
        [this](std::string_view value) {
            sourceLoader.addDirPrefix(value);
            return "";
        },
        "Directory prefix to prepend to source file paths when the file is not found at "
        "the listed path. Multiple prefixes are tried in the order they are specified. "
        "Must be specified before the source files that may need it.",
        "<prefix>", CommandLineFlags::CommaList);

    cmdLine.add(
        "-Y,--libext,+libext",
        [this](std::string_view value) {
            sourceLoader.addSearchExtension(value);
            return "";
        },
        "Additional library file extensions to search", "<ext>", CommandLineFlags::CommaList);

    cmdLine.add(
        "--exclude-ext",
        [this](std::string_view value) {
            options.excludeExts.emplace(std::string(value));
            return "";
        },
        "Exclude provided source files with these extensions", "<ext>",
        CommandLineFlags::CommaList);

    cmdLine.setPositional(
        [this](std::string_view value) {
            if (!options.excludeExts.empty()) {
                if (size_t extIndex = value.find_last_of('.'); extIndex != std::string_view::npos) {
                    if (options.excludeExts.count(std::string(value.substr(extIndex + 1))))
                        return "";
                }
            }

            sourceLoader.addFiles(value);
            return "";
        },
        "files");

    cmdLine.add(
        "-f",
        [this](std::string_view value) {
            processCommandFiles(value, /* makeRelative */ false, /* separateUnit */ false);
            return "";
        },
        "One or more command files containing additional program options. "
        "Paths in the file are considered relative to the current directory.",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    cmdLine.add(
        "-F",
        [this](std::string_view value) {
            processCommandFiles(value, /* makeRelative */ true, /* separateUnit */ false);
            return "";
        },
        "One or more command files containing additional program options. "
        "Paths in the file are considered relative to the file itself.",
        "<file-pattern>[,...]", CommandLineFlags::CommaList);

    // Dependency files
    cmdLine.add("--depfile-target", options.depfileTarget,
                "Output depfile lists in makefile format, creating the file with "
                "`<target>:` as the make target");
    cmdLine.add("--Mall,--all-deps", options.allDepfile,
                "Generate dependency file list of all files used during parsing", "<file>",
                CommandLineFlags::FilePath);
    cmdLine.add("--Minclude,--include-deps", options.includeDepfile,
                "Generate dependency file list of just include files that were "
                "used during parsing",
                "<file>", CommandLineFlags::FilePath);
    cmdLine.add("--Mmodule,--module-deps", options.moduleDepfile,
                "Generate dependency file list of source files parsed, excluding include files",
                "<file>", CommandLineFlags::FilePath);
    cmdLine.add("--depfile-trim", options.depfileTrim,
                "Trim unreferenced files before generating dependency lists "
                "(also implies --depfile-sort)");
    cmdLine.add("--depfile-sort", options.depfileSort,
                "Topologically sort the emitted files in dependency lists");

    // Analysis modifiers
    auto addAnalysisFlag = [&](AnalysisFlags flag, std::string_view name, std::string_view desc) {
        auto [it, inserted] = options.analysisFlags.emplace(flag, std::nullopt);
        SLANG_ASSERT(inserted);
        cmdLine.add(name, it->second, desc);
    };

    addAnalysisFlag(AnalysisFlags::FullCaseUniquePriority, "--dfa-unique-priority",
                    "Respect the 'unique' and 'priority' keywords when analyzing data flow "
                    "through case statements");
    addAnalysisFlag(AnalysisFlags::FullCaseFourState, "--dfa-four-state",
                    "Require that case items cover X and Z bits to assume full coverage "
                    "in data flow analysis");
    addAnalysisFlag(
        AnalysisFlags::AllowMultiDrivenLocals, "--allow-multi-driven-locals",
        "Allow subroutine local variables to be driven from multiple always_comb/_ff blocks");
    addAnalysisFlag(AnalysisFlags::AllowDupInitialDrivers, "--allow-dup-initial-drivers",
                    "Allow signals driven in an always_comb or always_ff block to also be driven "
                    "by initial blocks");

    cmdLine.add("--max-case-analysis-steps", options.maxCaseAnalysisSteps,
                "Maximum number of steps that can occur during case analysis before giving up",
                "<steps>");
    cmdLine.add("--max-loop-analysis-steps", options.maxLoopAnalysisSteps,
                "Maximum number of steps that can occur during loop analysis before giving up",
                "<steps>");
}

[[nodiscard]] bool Driver::parseCommandLine(std::string_view argList,
                                            CommandLine::ParseOptions parseOptions) {
    if (!cmdLine.parse(argList, parseOptions)) {
        for (auto& err : cmdLine.getErrors())
            OS::printE(fmt::format("{}\n", err));
        return false;
    }
    return !anyFailedLoads;
}

bool Driver::processCommandFiles(std::string_view pattern, bool makeRelative, bool separateUnit) {
    auto onError = [this](const auto& name, std::error_code ec) {
        printError(fmt::format("command file '{}': {}", name, ec.message()));
        anyFailedLoads = true;
        return false;
    };

    SmallVector<fs::path> files;
    std::error_code globEc;
    svGlob({}, pattern, GlobMode::Files, files, /* expandEnvVars */ false, globEc);
    if (globEc)
        return onError(pattern, globEc);

    for (auto& path : files) {
        SmallVector<char> buffer;
        if (auto readEc = OS::readFile(path, buffer))
            return onError(getU8Str(path), readEc);

        if (!activeCommandFiles.insert(path).second) {
            printError(
                fmt::format("command file '{}' includes itself recursively", getU8Str(path)));
            anyFailedLoads = true;
            return false;
        }

        fs::path currPath;
        std::error_code ec;
        if (makeRelative) {
            currPath = fs::current_path(ec);
            fs::current_path(path.parent_path(), ec);
        }

        SLANG_ASSERT(!buffer.empty());
        buffer.pop_back();
        std::string_view argStr(buffer.data(), buffer.size());

        bool result;
        if (separateUnit) {
            result = parseUnitListing(argStr);
        }
        else {
            CommandLine::ParseOptions parseOpts;
            parseOpts.expandEnvVars = true;
            parseOpts.ignoreProgramName = true;
            parseOpts.supportComments = true;
            parseOpts.ignoreDuplicates = true;
            result = parseCommandLine(argStr, parseOpts);
        }

        if (makeRelative)
            fs::current_path(currPath, ec);

        activeCommandFiles.erase(path);

        if (!result) {
            anyFailedLoads = true;
            return false;
        }
    }

    return true;
}

bool Driver::processOptions() {
    bool showColors;
    if (options.colorDiags.has_value())
        showColors = *options.colorDiags;
    else
        showColors = OS::fileSupportsColors(stderr);

    if (showColors) {
        OS::setStderrColorsEnabled(true);
        if (OS::fileSupportsColors(stdout))
            OS::setStdoutColorsEnabled(true);
    }

    if (options.languageVersion.has_value()) {
        if (options.languageVersion == "1364-2005")
            languageVersion = LanguageVersion::v1364_2005;
        else if (options.languageVersion == "1800-2017")
            languageVersion = LanguageVersion::v1800_2017;
        else if (options.languageVersion == "1800-2023" || options.languageVersion == "latest")
            languageVersion = LanguageVersion::v1800_2023;
        else {
            printError(
                fmt::format("invalid value for --std option: '{}'", *options.languageVersion));
            return false;
        }
    }

    if (options.compat.has_value()) {
        std::initializer_list<CompilationFlags> compFlags;
        std::initializer_list<AnalysisFlags> analysisFlags;
        if (options.compat == CompatMode::Vcs) {
            compFlags = vcsCompFlags;
            analysisFlags = vcsAnalysisFlags;
        }
        else {
            compFlags = allCompFlags;
            analysisFlags = allAnalysisFlags;
        }

        for (auto flag : compFlags) {
            auto& option = options.compilationFlags.at(flag);
            if (!option.has_value())
                option = true;
        }

        for (auto flag : analysisFlags) {
            auto& option = options.analysisFlags.at(flag);
            if (!option.has_value())
                option = true;
        }
    }

    if (options.librariesInheritMacros == true && !options.singleUnit.value_or(false)) {
        printError("--single-unit must be set when --libraries-inherit-macros is used");
        return false;
    }

    if (options.timeScale.has_value() && !TimeScale::fromString(*options.timeScale)) {
        printError(fmt::format("invalid value for time scale option: '{}'", *options.timeScale));
        return false;
    }

    if (options.lintMode()) {
        auto& opt = options.compilationFlags.at(CompilationFlags::IgnoreUnknownModules);
        if (!opt.has_value())
            opt = true;
    }

    if (!options.translateOffOptions.empty()) {
        bool anyBad = false;
        for (auto& fmtStr : options.translateOffOptions) {
            bool bad = false;
            auto parts = splitString(fmtStr, ',');
            if (parts.size() != 3)
                bad = true;

            for (auto part : parts) {
                if (part.empty())
                    bad = true;

                for (char c : part) {
                    if (!isAlphaNumeric(c) && c != '_')
                        bad = true;
                }
            }

            if (bad)
                printError(fmt::format("invalid format for translate-off-format: '{}'", fmtStr));
            else
                translateOffFormats.emplace_back(parts[0], parts[1], parts[2]);

            anyBad |= bad;
        }

        if (anyBad)
            return false;
    }

    if (options.disableLocalIncludes == true)
        sourceManager.setDisableLocalIncludes(true);

    if (!reportLoadErrors())
        return false;

    if (!sourceLoader.hasFiles()) {
        printError("no input files");
        return false;
    }

    if (options.diagJson.has_value()) {
        jsonWriter = std::make_unique<JsonWriter>();
        jsonWriter->setPrettyPrint(true);
        jsonWriter->startArray();

        jsonDiagClient = std::make_shared<JsonDiagnosticClient>(*jsonWriter);
        jsonDiagClient->showAbsPaths(options.diagAbsPaths.value_or(false));
        jsonDiagClient->setColumnUnit(options.diagColumnUnit.value_or(ColumnUnit::Display));
        diagEngine.addClient(jsonDiagClient);
    }

    auto& tdc = *textDiagClient;
    tdc.showColors(showColors);
    tdc.showColumn(options.diagColumn.value_or(true));
    tdc.setColumnUnit(options.diagColumnUnit.value_or(ColumnUnit::Display));
    tdc.showLocation(options.diagLocation.value_or(true));
    tdc.showSourceLine(options.diagSourceLine.value_or(true));
    tdc.showOptionName(options.diagOptionName.value_or(true));
    tdc.showIncludeStack(options.diagIncludeStack.value_or(true));
    tdc.showMacroExpansion(options.diagMacroExpansion.value_or(true));
    tdc.showAbsPaths(options.diagAbsPaths.value_or(false));
    tdc.showHierarchyInstance(options.diagHierarchy.value_or(ShowHierarchyPathOption::Auto));

    diagEngine.setErrorLimit((int)options.errorLimit.value_or(20));

    // Some tools violate the standard in various ways, but in order to allow
    // compatibility with these tools we change the respective errors into a
    // suppressible warning that we promote to an error by default. This allows
    // the user to turn this back into a warning, or turn it off altogether.

    if (options.compat != CompatMode::All) {
        diagEngine.setSeverity(diag::DuplicateDefinition, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::BadProceduralForce, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::UnknownSystemName, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::NonstandardStringConcat, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::MixedVarAssigns, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::MultipleContAssigns, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::MultipleAlwaysAssigns, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::MisplacedTrailingSeparator, DiagnosticSeverity::Error);
    }

    if (options.compat == CompatMode::Vcs || options.compat == CompatMode::All) {
        diagEngine.setSeverity(diag::StaticInitializerMustBeExplicit, DiagnosticSeverity::Ignored);
        diagEngine.setSeverity(diag::ImplicitConvert, DiagnosticSeverity::Ignored);
        diagEngine.setSeverity(diag::BadFinishNum, DiagnosticSeverity::Ignored);
        diagEngine.setSeverity(diag::NonstandardSysFunc, DiagnosticSeverity::Ignored);
        diagEngine.setSeverity(diag::NonstandardForeach, DiagnosticSeverity::Ignored);
        diagEngine.setSeverity(diag::NonstandardDist, DiagnosticSeverity::Ignored);
    }
    else {
        // These warnings are set to Error severity by default, unless we're in vcs compat mode.
        // The user can always downgrade via warning options, which get set after this.
        diagEngine.setSeverity(diag::IndexOOB, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::RangeOOB, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::RangeWidthOOB, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::ImplicitNamedPortTypeMismatch, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::SplitDistWeightOp, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::DPIPureTask, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::SpecifyPathConditionExpr, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::SolveBeforeDisallowed, DiagnosticSeverity::Error);
        diagEngine.setSeverity(diag::DynamicNotProcedural, DiagnosticSeverity::Error);
    }

    Diagnostics optionDiags = diagEngine.setWarningOptions(options.warningOptions);
    for (auto& diag : optionDiags)
        diagEngine.issue(diag);

    return true;
}

template<typename TGenerator>
static std::string generateRandomAlphaString(TGenerator& gen, size_t len) {
    static constexpr auto chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                  "abcdefghijklmnopqrstuvwxyz"sv;
    auto result = std::string(len, '\0');
    std::ranges::generate_n(begin(result), ptrdiff_t(len), [&] {
        return chars[getUniformIntDist(gen, size_t(0), chars.size() - 1)];
    });
    return result;
}

bool Driver::runPreprocessor(bool includeComments, bool includeDirectives, bool obfuscateIds,
                             bool useFixedObfuscationSeed) {
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, createParseOptionBag());

    auto buffers = sourceLoader.loadSources();
    for (auto it = buffers.rbegin(); it != buffers.rend(); it++)
        preprocessor.pushSource(*it);

    SyntaxPrinter output;
    output.setIncludeComments(includeComments);
    output.setIncludeDirectives(includeDirectives);

    std::optional<std::mt19937> rng;
    flat_hash_map<std::string, std::string> obfuscationMap;

    if (obfuscateIds) {
        if (useFixedObfuscationSeed)
            rng.emplace();
        else
            rng = createRandomGenerator<std::mt19937>();
    }

    while (true) {
        Token token = preprocessor.next();
        if (token.kind == TokenKind::IntegerBase) {
            // This is needed for the case where obfuscation is enabled,
            // the digits of a vector literal may be lexed initially as
            // an identifier and we don't have the parser here to fix things
            // up for us.
            do {
                output.print(token);
                token = preprocessor.next();
            } while (SyntaxFacts::isPossibleVectorDigit(token.kind));
        }

        if (obfuscateIds && token.kind == TokenKind::Identifier) {
            auto name = std::string(token.valueText());
            auto translation = obfuscationMap.find(name);
            if (translation == obfuscationMap.end()) {
                auto newName = generateRandomAlphaString(*rng, 16);
                translation = obfuscationMap.emplace(name, newName).first;
            }
            token = token.withRawText(alloc, translation->second);
        }

        output.print(token);
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    // Only print diagnostics if actual errors occurred.
    for (auto& diag : diagnostics) {
        if (diag.isError()) {
            OS::printE(fmt::format("{}", DiagnosticEngine::reportAll(sourceManager, diagnostics)));
            return false;
        }
    }

    OS::print(fmt::format("{}\n", output.str()));
    return true;
}

void Driver::reportMacros() {
    Bag optionBag;
    addParseOptions(optionBag);

    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, optionBag);

    auto buffers = sourceLoader.loadSources();
    for (auto it = buffers.rbegin(); it != buffers.rend(); it++)
        preprocessor.pushSource(*it);

    while (true) {
        Token token = preprocessor.next();
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    for (auto macro : preprocessor.getDefinedMacros()) {
        SyntaxPrinter printer;
        printer.setIncludeComments(false);
        printer.setIncludeTrivia(false);
        printer.print(macro->name);

        printer.setIncludeTrivia(true);
        if (macro->formalArguments)
            printer.print(*macro->formalArguments);

        if (!macro->body.empty() && macro->body[0].trivia().empty())
            printer.append(" "sv);

        printer.print(macro->body);

        OS::print(fmt::format("{}\n", printer.str()));
    }
}

static std::string getProximatePathStr(const fs::path& path) {
    std::error_code ec;
    auto file = fs::proximate(path, ec);
    if (ec)
        file = path;

    return getU8Str(file);
}

static std::vector<const SyntaxTree*> getSortedDependencies(
    Driver& driver, std::span<std::shared_ptr<SyntaxTree>> trees, bool trim) {

    // Map all declared modules, classes, etc to their containing syntax trees.
    flat_hash_map<std::string_view, const SyntaxTree*> nameToTree;
    for (auto& tree : trees) {
        for (auto name : tree->getMetadata().getDeclaredSymbols())
            nameToTree.emplace(name, tree.get());
    }

    struct Deps {
        std::vector<const SyntaxTree*> childTrees;
        std::vector<std::string_view> missingNames;
    };
    flat_hash_map<const SyntaxTree*, Deps> treeToDeps;
    flat_hash_map<std::string_view, const SyntaxTree*> missingToTree;

    // For each syntax tree, build a list of child trees that depend on it
    // based on references to modules, classes, etc.
    for (auto& tree : trees) {
        Deps deps;
        flat_hash_set<const SyntaxTree*> seenTrees;
        flat_hash_set<std::string_view> seenMissing;

        for (auto ref : tree->getMetadata().getReferencedSymbols()) {
            if (auto it = nameToTree.find(ref); it != nameToTree.end()) {
                if (seenTrees.insert(it->second).second)
                    deps.childTrees.push_back(it->second);
            }
            else if (seenMissing.insert(ref).second) {
                deps.missingNames.push_back(ref);
                missingToTree.emplace(ref, tree.get());
            }
        }

        treeToDeps.emplace(tree.get(), std::move(deps));
    }

    // Topologically sort the trees based on their dependencies.
    std::vector<const SyntaxTree*> results;
    flat_hash_set<const SyntaxTree*> visited;
    std::function<void(const SyntaxTree*)> dfsVisit = [&](const SyntaxTree* tree) {
        if (!visited.insert(tree).second)
            return;

        if (auto it = treeToDeps.find(tree); it != treeToDeps.end()) {
            for (auto dep : it->second.childTrees)
                dfsVisit(dep);

            for (auto name : it->second.missingNames) {
                driver.printWarning(fmt::format("'{}' not found in any source file", name));

                // Print one representative note for where this is referenced.
                if (auto missingIt = missingToTree.find(name); missingIt != missingToTree.end()) {
                    auto buffers = missingIt->second->getSourceBufferIds();
                    if (!buffers.empty()) {
                        driver.printNote(fmt::format(
                            "referenced in file '{}'",
                            getProximatePathStr(driver.sourceManager.getFullPath(buffers[0]))));
                    }
                }
            }
        }

        results.push_back(tree);
    };

    // If we are trimming, the initial set of trees to traverse is based on
    // the user specified set of top modules. Otherwise, we use all trees.
    if (trim) {
        if (driver.options.topModules.empty()) {
            driver.printWarning("using --depfile-trim with no top modules specified will always "
                                "result in an empty dependency file");
        }

        for (auto& name : driver.options.topModules) {
            if (auto it = nameToTree.find(name); it != nameToTree.end()) {
                dfsVisit(it->second);
            }
            else {
                driver.printWarning(
                    fmt::format("top module '{}' not found in any source file", name));
            }
        }
    }
    else {
        for (auto& tree : trees)
            dfsVisit(tree.get());
    }

    return results;
}

void Driver::optionallyWriteDepFiles() {
    if (!options.includeDepfile && !options.moduleDepfile && !options.allDepfile)
        return;

    std::vector<const SyntaxTree*> depTrees;
    if (options.depfileTrim == true || options.depfileSort == true) {
        depTrees = getSortedDependencies(*this, syntaxTrees, options.depfileTrim == true);
    }
    else {
        depTrees.reserve(syntaxTrees.size());
        for (auto& tree : syntaxTrees)
            depTrees.push_back(tree.get());
    }

    auto writeDepFile = [&](const std::vector<std::string>& paths, std::string_view fileName) {
        FormatBuffer buffer;
        if (options.depfileTarget)
            buffer.format("{}: ", *options.depfileTarget);

        for (auto& path : paths) {
            buffer.append(path);

            // If depfileTarget is provided the delimiter is a space, otherwise a newline.
            if (options.depfileTarget)
                buffer.append(" ");
            else
                buffer.append("\n");
        }

        if (options.depfileTarget) {
            buffer.pop_back();
            buffer.append("\n");
        }

        OS::writeFile(fileName, buffer.str());
    };

    std::vector<std::string> includePaths;
    flat_hash_set<fs::path> seenPaths;
    if (options.includeDepfile || options.allDepfile) {
        for (auto& tree : depTrees) {
            for (auto& inc : tree->getIncludeDirectives()) {
                if (inc.isSystem)
                    continue;

                auto p = sourceManager.getFullPath(inc.buffer.id);
                if (seenPaths.insert(p).second)
                    includePaths.emplace_back(getProximatePathStr(p));
            }
        }

        if (options.includeDepfile)
            writeDepFile(includePaths, *options.includeDepfile);
    }

    std::vector<std::string> modulePaths;
    if (options.moduleDepfile || options.allDepfile) {
        for (auto& tree : depTrees) {
            for (auto bufferId : tree->getSourceBufferIds()) {
                auto path = sourceManager.getFullPath(bufferId);
                if (!path.empty())
                    modulePaths.emplace_back(getProximatePathStr(path));
            }
        }

        if (options.moduleDepfile)
            writeDepFile(modulePaths, *options.moduleDepfile);
    }

    if (options.allDepfile) {
        includePaths.insert(includePaths.end(), modulePaths.begin(), modulePaths.end());
        writeDepFile(includePaths, *options.allDepfile);
    }
}

bool Driver::parseAllSources() {
    syntaxTrees = sourceLoader.loadAndParseSources(createParseOptionBag());
    if (!reportLoadErrors())
        return false;

    Diagnostics pragmaDiags = diagEngine.setMappingsFromPragmas();
    for (auto& diag : pragmaDiags)
        diagEngine.issue(diag);

    return true;
}

Bag Driver::createParseOptionBag() const {
    Bag bag;
    addParseOptions(bag);
    return bag;
}

Bag Driver::createOptionBag() const {
    Bag bag;
    addParseOptions(bag);
    addCompilationOptions(bag);
    return bag;
}

void Driver::addParseOptions(Bag& bag) const {
    SourceOptions soptions;
    soptions.numThreads = options.numThreads;
    soptions.singleUnit = options.singleUnit == true;
    soptions.onlyLint = options.lintMode();
    soptions.librariesInheritMacros = options.librariesInheritMacros == true;

    PreprocessorOptions ppoptions;
    ppoptions.predefines = options.defines;
    ppoptions.undefines = options.undefines;
    ppoptions.predefineSource = "<command-line>";
    ppoptions.languageVersion = languageVersion;
    ppoptions.keywordMapping = options.keywordMapping;
    if (options.maxIncludeDepth.has_value())
        ppoptions.maxIncludeDepth = *options.maxIncludeDepth;
    for (const auto& d : options.ignoreDirectives)
        ppoptions.ignoreDirectives.emplace(d);

    LexerOptions loptions;
    loptions.languageVersion = languageVersion;
    loptions.enableLegacyProtect = options.enableLegacyProtect == true;
    if (options.maxLexerErrors.has_value())
        loptions.maxErrors = *options.maxLexerErrors;

    if (loptions.enableLegacyProtect)
        loptions.commentHandlers["pragma"]["protect"] = {CommentHandler::Protect};

    for (auto& [common, start, end] : translateOffFormats)
        loptions.commentHandlers[common][start] = {CommentHandler::TranslateOff, end};

    loptions.commentHandlers["slang"]["lint_off"] = {CommentHandler::LintOff};
    loptions.commentHandlers["slang"]["lint_on"] = {CommentHandler::LintOn};
    loptions.commentHandlers["slang"]["lint_save"] = {CommentHandler::LintSave};
    loptions.commentHandlers["slang"]["lint_restore"] = {CommentHandler::LintRestore};

    ParserOptions poptions;
    poptions.languageVersion = languageVersion;
    if (options.maxParseDepth.has_value())
        poptions.maxRecursionDepth = *options.maxParseDepth;

    bag.set(soptions);
    bag.set(ppoptions);
    bag.set(loptions);
    bag.set(poptions);
}

void Driver::addCompilationOptions(Bag& bag) const {
    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;
    coptions.languageVersion = languageVersion;
    if (options.maxInstanceDepth.has_value())
        coptions.maxInstanceDepth = *options.maxInstanceDepth;
    if (options.maxGenerateSteps.has_value())
        coptions.maxGenerateSteps = *options.maxGenerateSteps;
    if (options.maxConstexprDepth.has_value())
        coptions.maxConstexprDepth = *options.maxConstexprDepth;
    if (options.maxConstexprSteps.has_value())
        coptions.maxConstexprSteps = *options.maxConstexprSteps;
    if (options.maxConstexprBacktrace.has_value())
        coptions.maxConstexprBacktrace = *options.maxConstexprBacktrace;
    if (options.maxInstanceArray.has_value())
        coptions.maxInstanceArray = *options.maxInstanceArray;
    if (options.maxEnumValues.has_value())
        coptions.maxEnumValues = *options.maxEnumValues;
    if (options.maxUDPCoverageNotes.has_value())
        coptions.maxUDPCoverageNotes = *options.maxUDPCoverageNotes;
    if (options.errorLimit.has_value())
        coptions.errorLimit = *options.errorLimit * 2;
    if (options.minTypMax.has_value())
        coptions.minTypMax = *options.minTypMax;

    for (auto& [flag, value] : options.compilationFlags) {
        if (value == true)
            coptions.flags |= flag;
    }

    for (auto& name : options.topModules)
        coptions.topModules.emplace(name);
    for (auto& opt : options.paramOverrides)
        coptions.paramOverrides.emplace_back(opt);
    for (auto& lib : options.libraryOrder)
        coptions.defaultLiblist.emplace_back(lib);

    if (options.timeScale.has_value())
        coptions.defaultTimeScale = TimeScale::fromString(*options.timeScale);

    bag.set(coptions);
}

analysis::AnalysisOptions Driver::getAnalysisOptions() const {
    using namespace slang::analysis;

    AnalysisOptions ao;
    ao.numThreads = options.numThreads.value_or(0);
    ao.flags |= AnalysisFlags::CheckUnused;
    if (options.maxCaseAnalysisSteps)
        ao.maxCaseAnalysisSteps = *options.maxCaseAnalysisSteps;
    if (options.maxLoopAnalysisSteps)
        ao.maxLoopAnalysisSteps = *options.maxLoopAnalysisSteps;

    for (auto& [flag, value] : options.analysisFlags) {
        if (value == true)
            ao.flags |= flag;
    }
    return ao;
}

std::unique_ptr<Compilation> Driver::createCompilation() {
    SourceLibrary* defaultLib;
    if (options.defaultLibName && !options.defaultLibName->empty())
        defaultLib = sourceLoader.getOrAddLibrary(*options.defaultLibName);
    else
        defaultLib = sourceLoader.getOrAddLibrary("work");

    SLANG_ASSERT(defaultLib);
    defaultLib->isDefault = true;

    auto compilation = std::make_unique<Compilation>(createOptionBag(), defaultLib);
    for (auto& tree : sourceLoader.getLibraryMaps())
        compilation->addSyntaxTree(tree);
    for (auto& tree : syntaxTrees)
        compilation->addSyntaxTree(tree);

    return compilation;
}

bool Driver::reportParseDiags() {
    Diagnostics diags;
    for (auto& tree : sourceLoader.getLibraryMaps())
        diags.append_range(tree->diagnostics());
    for (auto& tree : syntaxTrees)
        diags.append_range(tree->diagnostics());

    diags.sort(sourceManager);
    for (auto& diag : diags)
        diagEngine.issue(diag);

    OS::printE(fmt::format("{}", textDiagClient->getString()));
    return diagEngine.getNumErrors() == 0;
}

void Driver::reportCompilation(Compilation& compilation, bool quiet) {
    if (!quiet) {
        auto topInstances = compilation.getRoot().topInstances;
        if (!topInstances.empty()) {
            OS::print(fg(textDiagClient->warningColor), "Top level design units:\n");
            for (auto inst : topInstances)
                OS::print(fmt::format("    {}\n", inst->name));
            OS::print("\n");
        }
    }

    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);
}

std::unique_ptr<AnalysisManager> Driver::runAnalysis(ast::Compilation& compilation) {

    compilation.getAllDiagnostics();
    compilation.freeze();

    auto analysisManager = std::make_unique<analysis::AnalysisManager>(getAnalysisOptions());

    // We can't / shouldn't run analysis in lint-only mode.
    // We'll just return an empty analysis manager in that case.
    if (!options.lintMode()) {
        analysisManager->analyze(compilation);

        for (auto& diag : analysisManager->getDiagnostics())
            diagEngine.issue(diag);
    }

    compilation.unfreeze();

    return analysisManager;
}

bool Driver::reportDiagnostics(bool quiet) {
    bool hasDiagsStdout = false;
    bool succeeded = diagEngine.getNumErrors() == 0;

    if (jsonWriter)
        jsonWriter->endArray();

    if (options.diagJson == "-") {
        // If we're printing JSON diagnostics to stdout don't also
        // print the text diagnostics.
        hasDiagsStdout = true;
        OS::print(jsonWriter->view());
    }
    else {
        std::string diagStr = textDiagClient->getString();
        hasDiagsStdout = diagStr.size() > 1;
        OS::printE(diagStr);

        if (jsonWriter)
            OS::writeFile(*options.diagJson, jsonWriter->view());
    }

    if (!quiet) {
        if (hasDiagsStdout)
            OS::print("\n");

        if (succeeded)
            OS::print(fg(textDiagClient->highlightColor), "Build succeeded: ");
        else
            OS::print(fg(textDiagClient->errorColor), "Build failed: ");

        OS::print(fmt::format("{} error{}, {} warning{}\n", diagEngine.getNumErrors(),
                              diagEngine.getNumErrors() == 1 ? "" : "s",
                              diagEngine.getNumWarnings(),
                              diagEngine.getNumWarnings() == 1 ? "" : "s"));
    }

    return succeeded;
}

bool Driver::runFullCompilation(bool quiet) {
    auto compilation = createCompilation();
    reportCompilation(*compilation, quiet);
    runAnalysis(*compilation);
    return reportDiagnostics(quiet);
}

bool Driver::parseUnitListing(std::string_view text) {
    CommandLine unitCmdLine;
    std::vector<std::string> includes;
    unitCmdLine.add("-I,--include-directory,+incdir", includes, "", "",
                    CommandLineFlags::CommaList);

    std::vector<std::string> defines;
    unitCmdLine.add("-D,--define-macro,+define", defines, "");

    std::optional<std::string> libraryName;
    unitCmdLine.add("--library", libraryName, "");

    unitCmdLine.add(
        "-C",
        [this](std::string_view value) {
            processCommandFiles(value, /* makeRelative */ true, /* separateUnit */ true);
            return "";
        },
        "", "", CommandLineFlags::CommaList);

    std::vector<std::string> files;
    unitCmdLine.setPositional(
        [&](std::string_view value) {
            if (!options.excludeExts.empty()) {
                if (size_t extIndex = value.find_last_of('.'); extIndex != std::string_view::npos) {
                    if (options.excludeExts.count(std::string(value.substr(extIndex + 1))))
                        return "";
                }
            }

            files.push_back(std::string(value));
            return "";
        },
        "");

    CommandLine::ParseOptions parseOpts;
    parseOpts.expandEnvVars = true;
    parseOpts.ignoreProgramName = true;
    parseOpts.supportComments = true;
    parseOpts.ignoreDuplicates = true;

    if (!unitCmdLine.parse(text, parseOpts)) {
        for (auto& err : unitCmdLine.getErrors())
            OS::printE(fmt::format("{}\n", err));
        return false;
    }

    sourceLoader.addSeparateUnit(files, includes, std::move(defines),
                                 std::move(libraryName).value_or(std::string()));

    return true;
}

std::string Driver::parseMapKeywordVersion(std::string_view value) {
    const size_t plusIndex = value.find_first_of('+');
    if (plusIndex == std::string_view::npos)
        return fmt::format("missing '+' in argument '{}'", value);

    auto versionStr = value.substr(0, plusIndex);
    auto keywordVersion = LexerFacts::getKeywordVersion(versionStr);
    if (!keywordVersion.has_value())
        return fmt::format("'{}' is not a valid keyword version", versionStr);

    value = value.substr(plusIndex + 1);
    while (!value.empty()) {
        auto comma = value.find_first_of(',');
        options.keywordMapping.push_back({std::string(value.substr(0, comma)), *keywordVersion});

        if (comma == std::string_view::npos)
            value = {};
        else
            value = value.substr(comma + 1);
    }

    return "";
}

void Driver::addLibraryFiles(std::string_view pattern) {
    // Parse the pattern; there's an optional leading library name
    // followed by an equals sign. If not there, we use the default
    // library (represented by the empty string).
    std::string_view libraryName;
    auto index = pattern.find_first_of('=');
    if (index != std::string_view::npos) {
        libraryName = pattern.substr(0, index);
        pattern = pattern.substr(index + 1);
    }
    sourceLoader.addLibraryFiles(libraryName, pattern);
}

bool Driver::reportLoadErrors() {
    if (auto errors = sourceLoader.getErrors(); !errors.empty()) {
        for (auto& err : errors)
            printError(err);
        return false;
    }
    return true;
}

void Driver::printError(const std::string& message) {
    OS::printE(fg(textDiagClient->errorColor), "error: ");
    OS::printE(message);
    OS::printE("\n");
}

void Driver::printWarning(const std::string& message) {
    OS::printE(fg(textDiagClient->warningColor), "warning: ");
    OS::printE(message);
    OS::printE("\n");
}

void Driver::printNote(const std::string& message) {
    OS::printE(fg(textDiagClient->noteColor), "  note: ");
    OS::printE(message);
    OS::printE("\n");
}

bool Driver::Options::lintMode() const {
    return compilationFlags.at(CompilationFlags::LintMode) == true;
}

} // namespace slang::driver
