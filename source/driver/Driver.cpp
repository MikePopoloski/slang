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

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/util/Random.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace ast;
using namespace parsing;
using namespace syntax;

Driver::Driver() : diagEngine(sourceManager) {
    diagClient = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(diagClient);
}

void Driver::addStandardArgs() {
    // Include paths
    cmdLine.add("-I,--include-directory,+incdir", options.includeDirs,
                "Additional include search paths", "<dir>", /* isFileName */ true);
    cmdLine.add("--isystem", options.includeSystemDirs, "Additional system include search paths",
                "<dir>",
                /* isFileName */ true);
    cmdLine.add("-y,--libdir", options.libDirs,
                "Library search paths, which will be searched for missing modules", "<dir>",
                /* isFileName */ true);
    cmdLine.add("-Y,--libext", options.libExts, "Additional library file extensions to search",
                "<ext>");
    cmdLine.add(
        "--exclude-ext",
        [this](string_view value) {
            options.excludeExts.emplace(std::string(value));
            return "";
        },
        "Exclude provided source files with these extensions", "<ext>");

    // Preprocessor
    cmdLine.add("-D,--define-macro,+define", options.defines,
                "Define <macro> to <value> (or 1 if <value> ommitted) in all source files",
                "<macro>=<value>");
    cmdLine.add("-U,--undefine-macro", options.undefines,
                "Undefine macro name at the start of all source files", "<macro>");
    cmdLine.add("--max-include-depth", options.maxIncludeDepth,
                "Maximum depth of nested include files allowed", "<depth>");
    cmdLine.add("--libraries-inherit-macros", options.librariesInheritMacros,
                "If true, library files will inherit macro definitions from the primary source "
                "files. --single-unit must also be passed when this option is used.");

    // Legacy vendor commands support
    cmdLine.add(
        "--cmd-ignore", [this](string_view value) { return cmdLine.addIgnoreCommand(value); },
        "Define rule to ignore vendor command <vendor_cmd> with its following <N> parameters.\n"
        "A command of the form +xyz will also match any vendor command of the form +xyz+abc,\n"
        "as +abc is the command's argument, and doesn't need to be matched.",
        "<vendor_cmd>,<N>");
    cmdLine.add(
        "--cmd-rename", [this](string_view value) { return cmdLine.addRenameCommand(value); },
        "Define rule to rename vendor command <vendor_cmd> into existing <slang_cmd>",
        "<vendor_cmd>,<slang_cmd>");
    cmdLine.add("--ignore-directive", options.ignoreDirectives,
                "Ignore preprocessor directive and all its arguments until EOL", "<directive>");

    // Parsing
    cmdLine.add("--max-parse-depth", options.maxParseDepth,
                "Maximum depth of nested language constructs allowed", "<depth>");
    cmdLine.add("--max-lexer-errors", options.maxLexerErrors,
                "Maximum number of errors that can occur during lexing before the rest of the file "
                "is skipped",
                "<count>");

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
    cmdLine.add("--compat", options.compat,
                "Attempt to increase compatibility with the specified tool", "vcs");
    cmdLine.add("-T,--timing", options.minTypMax,
                "Select which value to consider in min:typ:max expressions", "min|typ|max");
    cmdLine.add("--timescale", options.timeScale,
                "Default time scale to use for design elements that don't specify one explicitly",
                "<base>/<precision>");
    cmdLine.add("--allow-use-before-declare", options.allowUseBeforeDeclare,
                "Don't issue an error for use of names before their declarations.");
    cmdLine.add("--ignore-unknown-modules", options.ignoreUnknownModules,
                "Don't issue an error for instantiations of unknown modules, "
                "interface, and programs.");
    cmdLine.add("--relax-enum-conversions", options.relaxEnumConversions,
                "Allow all integral types to convert implicitly to enum types.");
    cmdLine.add("--allow-hierarchical-const", options.allowHierarchicalConst,
                "Allow hierarchical references in constant expressions.");
    cmdLine.add("--allow-dup-initial-drivers", options.allowDupInitialDrivers,
                "Allow signals driven in an always_comb or always_ff block to also be driven "
                "by initial blocks.");
    cmdLine.add("--strict-driver-checking", options.strictDriverChecking,
                "Perform strict driver checking, which currently means disabling "
                "procedural 'for' loop unrolling.");
    cmdLine.add("--lint-only", options.onlyLint,
                "Only perform linting of code, don't try to elaborate a full hierarchy");
    cmdLine.add("--top", options.topModules,
                "One or more top-level modules to instantiate "
                "(instead of figuring it out automatically)",
                "<name>");
    cmdLine.add("-G", options.paramOverrides,
                "One or more parameter overrides to apply when "
                "instantiating top-level modules",
                "<name>=<value>");

    // Diagnostics control
    cmdLine.add("-W", options.warningOptions, "Control the specified warning", "<warning>");
    cmdLine.add("--color-diagnostics", options.colorDiags,
                "Always print diagnostics in color."
                "If this option is unset, colors will be enabled if a color-capable "
                "terminal is detected.");
    cmdLine.add("--diag-column", options.diagColumn, "Show column numbers in diagnostic output.");
    cmdLine.add("--diag-location", options.diagLocation,
                "Show location information in diagnostic output.");
    cmdLine.add("--diag-source", options.diagSourceLine,
                "Show source line or caret info in diagnostic output.");
    cmdLine.add("--diag-option", options.diagOptionName, "Show option names in diagnostic output.");
    cmdLine.add("--diag-include-stack", options.diagIncludeStack,
                "Show include stacks in diagnostic output.");
    cmdLine.add("--diag-macro-expansion", options.diagMacroExpansion,
                "Show macro expansion backtraces in diagnostic output.");
    cmdLine.add("--diag-hierarchy", options.diagHierarchy,
                "Show hierarchy locations in diagnostic output.");
    cmdLine.add("--error-limit", options.errorLimit,
                "Limit on the number of errors that will be printed. Setting this to zero will "
                "disable the limit.",
                "<limit>");
    cmdLine.add("--suppress-warnings", options.suppressWarningsPaths,
                "One or more paths in which to suppress warnings", "<filename>",
                /* isFileName */ true);

    // File lists
    cmdLine.add("--single-unit", options.singleUnit,
                "Treat all input files as a single compilation unit");

    cmdLine.add("-v", options.libraryFiles,
                "One or more library files, which are separate compilation units "
                "where modules are not automatically instantiated.",
                "<filename>", /* isFileName */ true);

    cmdLine.setPositional(
        [this](string_view fileName) {
            if (!options.excludeExts.empty()) {
                if (size_t extIndex = fileName.find_last_of('.'); extIndex != string_view::npos) {
                    if (options.excludeExts.count(std::string(fileName.substr(extIndex + 1))))
                        return "";
                }
            }

            SourceBuffer buffer = readSource(fileName);
            if (!buffer)
                anyFailedLoads = true;

            buffers.push_back(buffer);
            return "";
        },
        "files", /* isFileName */ true);

    cmdLine.add(
        "-f",
        [this](string_view fileName) {
            if (!processCommandFile(fileName, /* makeRelative */ false))
                anyFailedLoads = true;
            return "";
        },
        "One or more command files containing additional program options. "
        "Paths in the file are considered relative to the current directory.",
        "<filename>", /* isFileName */ true);

    cmdLine.add(
        "-F",
        [this](string_view fileName) {
            if (!processCommandFile(fileName, /* makeRelative */ true))
                anyFailedLoads = true;
            return "";
        },
        "One or more command files containing additional program options. "
        "Paths in the file are considered relative to the file itself.",
        "<filename>", /* isFileName */ true);
}

[[nodiscard]] bool Driver::parseCommandLine(string_view argList) {
    if (!cmdLine.parse(argList)) {
        for (auto& err : cmdLine.getErrors())
            OS::printE(fmt::format("{}\n", err));
        return false;
    }
    return !anyFailedLoads;
}

SourceBuffer Driver::readSource(string_view fileName) {
    SourceBuffer buffer = sourceManager.readSource(widen(fileName));
    if (!buffer) {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE(fmt::format("no such file or directory: '{}'\n", fileName));
    }
    return buffer;
}

bool Driver::processCommandFile(string_view fileName, bool makeRelative) {
    std::error_code ec;
    fs::path path = fs::canonical(widen(fileName), ec);
    std::vector<char> buffer;
    if (ec || !OS::readFile(path, buffer)) {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE(fmt::format("no such file or directory: '{}'\n", fileName));
        return false;
    }

    fs::path currPath;
    if (makeRelative) {
        currPath = fs::current_path();
        fs::current_path(path.parent_path());
    }

    CommandLine::ParseOptions parseOpts;
    parseOpts.expandEnvVars = true;
    parseOpts.ignoreProgramName = true;
    parseOpts.supportComments = true;
    parseOpts.ignoreDuplicates = true;

    ASSERT(!buffer.empty());
    buffer.pop_back();

    string_view argStr(buffer.data(), buffer.size());
    bool result = cmdLine.parse(argStr, parseOpts);

    if (makeRelative)
        fs::current_path(currPath);

    if (!result) {
        for (auto& err : cmdLine.getErrors())
            OS::printE(fmt::format("{}\n", err));
        return false;
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

    if (options.compat.has_value()) {
        if (options.compat == "vcs") {
            if (!options.allowHierarchicalConst.has_value())
                options.allowHierarchicalConst = true;
            if (!options.allowUseBeforeDeclare.has_value())
                options.allowUseBeforeDeclare = true;
            if (!options.relaxEnumConversions.has_value())
                options.relaxEnumConversions = true;
        }
        else {
            OS::printE(fg(diagClient->errorColor), "error: ");
            OS::printE(fmt::format("invalid value for compat option: '{}'", *options.compat));
            return false;
        }
    }

    if (options.minTypMax.has_value() && options.minTypMax != "min" && options.minTypMax != "typ" &&
        options.minTypMax != "max") {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE(fmt::format("invalid value for timing option: '{}'", *options.minTypMax));
        return false;
    }

    if (options.librariesInheritMacros == true && !options.singleUnit.value_or(false)) {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE("--single-unit must be set when --libraries-inherit-macros is used");
        return false;
    }

    if (options.timeScale.has_value() && !TimeScale::fromString(*options.timeScale)) {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE(fmt::format("invalid value for time scale option: '{}'", *options.timeScale));
        return false;
    }

    if (options.onlyLint == true && !options.ignoreUnknownModules.has_value())
        options.ignoreUnknownModules = true;

    for (const std::string& dir : options.includeDirs) {
        try {
            sourceManager.addUserDirectory(string_view(dir));
        }
        catch (const std::exception&) {
            OS::printE(fg(diagClient->warningColor), "warning: ");
            OS::printE(fmt::format("include directory '{}' does not exist\n", dir));
        }
    }

    for (const std::string& dir : options.includeSystemDirs) {
        try {
            sourceManager.addSystemDirectory(string_view(dir));
        }
        catch (const std::exception&) {
            OS::printE(fg(diagClient->warningColor), "warning: ");
            OS::printE(fmt::format("include directory '{}' does not exist\n", dir));
        }
    }

    if (anyFailedLoads)
        return false;

    if (buffers.empty() && options.libraryFiles.empty()) {
        OS::printE(fg(diagClient->errorColor), "error: ");
        OS::printE("no input files\n");
        return false;
    }

    auto& dc = *diagClient;
    dc.showColors(showColors);
    dc.showColumn(options.diagColumn.value_or(true));
    dc.showLocation(options.diagLocation.value_or(true));
    dc.showSourceLine(options.diagSourceLine.value_or(true));
    dc.showOptionName(options.diagOptionName.value_or(true));
    dc.showIncludeStack(options.diagIncludeStack.value_or(true));
    dc.showMacroExpansion(options.diagMacroExpansion.value_or(true));
    dc.showHierarchyInstance(options.diagHierarchy.value_or(true));

    diagEngine.setErrorLimit((int)options.errorLimit.value_or(20));
    diagEngine.setDefaultWarnings();

    // Some tools violate the standard in various ways, but in order to allow
    // compatibility with these tools, we change the respective errors into a
    // suppressible warning that we promote to an error by default, allowing
    // the user to turn this back into a warning, ot turn it off altogether.

    // allow ignoring duplicate module/interface/program definitions,
    diagEngine.setSeverity(diag::DuplicateDefinition, DiagnosticSeverity::Error);
    // allow procedural force on variable part-select
    diagEngine.setSeverity(diag::BadProceduralForce, DiagnosticSeverity::Error);

    if (options.compat == "vcs") {
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
    }

    for (const std::string& path : options.suppressWarningsPaths)
        diagEngine.addIgnorePath(fs::canonical(widen(path)));

    Diagnostics optionDiags = diagEngine.setWarningOptions(options.warningOptions);
    for (auto& diag : optionDiags)
        diagEngine.issue(diag);

    return true;
}

template<typename TGenerator>
static std::string generateRandomAlphanumericString(TGenerator& gen, size_t len) {
    static constexpr auto chars = "0123456789"
                                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                  "abcdefghijklmnopqrstuvwxyz"sv;
    auto result = std::string(len, '\0');
    std::generate_n(begin(result), len,
                    [&] { return chars[getUniformIntDist(gen, size_t(0), chars.size() - 1)]; });
    return result;
}

bool Driver::runPreprocessor(bool includeComments, bool includeDirectives, bool obfuscateIds,
                             bool useFixedObfuscationSeed) {
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, createOptionBag());

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
                auto newName = generateRandomAlphanumericString(*rng, 16);
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
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, createOptionBag());

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

bool Driver::parseAllSources() {
    bool singleUnit = options.singleUnit == true;
    bool onlyLint = options.onlyLint == true;

    auto optionBag = createOptionBag();
    if (singleUnit) {
        auto tree = SyntaxTree::fromBuffers(buffers, sourceManager, optionBag);
        if (onlyLint)
            tree->isLibrary = true;

        syntaxTrees.emplace_back(std::move(tree));
    }
    else {
        for (const SourceBuffer& buffer : buffers) {
            auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag);
            if (onlyLint)
                tree->isLibrary = true;

            syntaxTrees.emplace_back(std::move(tree));
        }
    }

    span<const DefineDirectiveSyntax* const> inheritedMacros;
    if (options.librariesInheritMacros == true)
        inheritedMacros = syntaxTrees.back()->getDefinedMacros();

    bool ok = true;
    for (auto& file : options.libraryFiles) {
        SourceBuffer buffer = readSource(file);
        if (!buffer) {
            ok = false;
            continue;
        }

        auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag, inheritedMacros);
        tree->isLibrary = true;
        syntaxTrees.emplace_back(std::move(tree));
    }

    if (!options.libDirs.empty()) {
        std::vector<fs::path> directories;
        directories.reserve(options.libDirs.size());
        for (auto& dir : options.libDirs)
            directories.emplace_back(widen(dir));

        flat_hash_set<string_view> uniqueExtensions;
        uniqueExtensions.emplace(".v"sv);
        uniqueExtensions.emplace(".sv"sv);
        for (auto& ext : options.libExts)
            uniqueExtensions.emplace(ext);

        std::vector<fs::path> extensions;
        for (auto ext : uniqueExtensions)
            extensions.emplace_back(widen(ext));

        // If library directories are specified, see if we have any unknown instantiations
        // or package names for which we should search for additional source files to load.
        flat_hash_set<string_view> knownNames;
        auto addKnownNames = [&](const std::shared_ptr<SyntaxTree>& tree) {
            auto& meta = tree->getMetadata();
            for (auto& [n, _] : meta.nodeMap) {
                auto decl = &n->as<ModuleDeclarationSyntax>();
                string_view name = decl->header->name.valueText();
                if (!name.empty())
                    knownNames.emplace(name);
            }

            for (auto classDecl : meta.classDecls) {
                string_view name = classDecl->name.valueText();
                if (!name.empty())
                    knownNames.emplace(name);
            }
        };

        auto findMissingNames = [&](const std::shared_ptr<SyntaxTree>& tree,
                                    flat_hash_set<string_view>& missing) {
            auto& meta = tree->getMetadata();
            for (auto name : meta.globalInstances) {
                if (knownNames.find(name) == knownNames.end())
                    missing.emplace(name);
            }

            for (auto idName : meta.classPackageNames) {
                string_view name = idName->identifier.valueText();
                if (!name.empty() && knownNames.find(name) == knownNames.end())
                    missing.emplace(name);
            }

            for (auto importDecl : meta.packageImports) {
                for (auto importItem : importDecl->items) {
                    string_view name = importItem->package.valueText();
                    if (!name.empty() && knownNames.find(name) == knownNames.end())
                        missing.emplace(name);
                }
            }
        };

        for (auto& tree : syntaxTrees)
            addKnownNames(tree);

        flat_hash_set<string_view> missingNames;
        for (auto& tree : syntaxTrees)
            findMissingNames(tree, missingNames);

        // Keep loading new files as long as we are making forward progress.
        flat_hash_set<string_view> nextMissingNames;
        while (true) {
            for (auto name : missingNames) {
                SourceBuffer buffer;
                for (auto& dir : directories) {
                    fs::path path(dir);
                    path /= name;

                    for (auto& ext : extensions) {
                        path.replace_extension(ext);
                        if (!sourceManager.isCached(path)) {
                            buffer = sourceManager.readSource(path);
                            if (buffer)
                                break;
                        }
                    }

                    if (buffer)
                        break;
                }

                if (buffer) {
                    auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
                                                       inheritedMacros);
                    tree->isLibrary = true;
                    syntaxTrees.emplace_back(tree);

                    addKnownNames(tree);
                    findMissingNames(tree, nextMissingNames);
                }
            }

            if (nextMissingNames.empty())
                break;

            missingNames = std::move(nextMissingNames);
            nextMissingNames.clear();
        }
    }

    if (ok) {
        Diagnostics pragmaDiags = diagEngine.setMappingsFromPragmas();
        for (auto& diag : pragmaDiags)
            diagEngine.issue(diag);
    }

    return ok;
}

Bag Driver::createOptionBag() const {
    PreprocessorOptions ppoptions;
    ppoptions.predefines = options.defines;
    ppoptions.undefines = options.undefines;
    ppoptions.predefineSource = "<command-line>";
    if (options.maxIncludeDepth.has_value())
        ppoptions.maxIncludeDepth = *options.maxIncludeDepth;
    for (const auto& d : options.ignoreDirectives)
        ppoptions.ignoreDirectives.emplace(d);

    LexerOptions loptions;
    if (options.maxLexerErrors.has_value())
        loptions.maxErrors = *options.maxLexerErrors;

    ParserOptions poptions;
    if (options.maxParseDepth.has_value())
        poptions.maxRecursionDepth = *options.maxParseDepth;

    CompilationOptions coptions;
    coptions.suppressUnused = false;
    coptions.scriptMode = false;
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
    if (options.errorLimit.has_value())
        coptions.errorLimit = *options.errorLimit * 2;
    if (options.onlyLint == true) {
        coptions.suppressUnused = true;
        coptions.lintMode = true;
    }
    if (options.allowHierarchicalConst == true)
        coptions.allowHierarchicalConst = true;
    if (options.allowDupInitialDrivers == true)
        coptions.allowDupInitialDrivers = true;
    if (options.relaxEnumConversions == true)
        coptions.relaxEnumConversions = true;
    if (options.strictDriverChecking == true)
        coptions.strictDriverChecking = true;
    if (options.ignoreUnknownModules == true)
        coptions.ignoreUnknownModules = true;
    if (options.allowUseBeforeDeclare == true)
        coptions.allowUseBeforeDeclare = true;

    for (auto& name : options.topModules)
        coptions.topModules.emplace(name);
    for (auto& opt : options.paramOverrides)
        coptions.paramOverrides.emplace_back(opt);

    if (options.minTypMax.has_value()) {
        if (options.minTypMax == "min")
            coptions.minTypMax = MinTypMax::Min;
        else if (options.minTypMax == "typ")
            coptions.minTypMax = MinTypMax::Typ;
        else if (options.minTypMax == "max")
            coptions.minTypMax = MinTypMax::Max;
    }

    if (options.timeScale.has_value())
        coptions.defaultTimeScale = TimeScale::fromString(*options.timeScale);

    Bag bag;
    bag.set(ppoptions);
    bag.set(loptions);
    bag.set(poptions);
    bag.set(coptions);

    return bag;
}

std::unique_ptr<Compilation> Driver::createCompilation() const {
    auto compilation = std::make_unique<Compilation>(createOptionBag());
    for (auto& tree : syntaxTrees)
        compilation->addSyntaxTree(tree);

    return compilation;
}

bool Driver::reportParseDiags() {
    auto compilation = createCompilation();
    for (auto& diag : compilation->getParseDiagnostics())
        diagEngine.issue(diag);

    OS::printE(fmt::format("{}", diagClient->getString()));
    return diagEngine.getNumErrors() == 0;
}

bool Driver::reportCompilation(Compilation& compilation, bool quiet) {
    if (!quiet) {
        auto topInstances = compilation.getRoot().topInstances;
        if (!topInstances.empty()) {
            OS::print(fg(diagClient->warningColor), "Top level design units:\n");
            for (auto inst : topInstances)
                OS::print(fmt::format("    {}\n", inst->name));
            OS::print("\n");
        }
    }

    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);

    bool succeeded = diagEngine.getNumErrors() == 0;

    std::string diagStr = diagClient->getString();
    OS::printE(fmt::format("{}", diagStr));

    if (!quiet) {
        if (diagStr.size() > 1)
            OS::print("\n");

        if (succeeded)
            OS::print(fg(diagClient->highlightColor), "Build succeeded: ");
        else
            OS::print(fg(diagClient->errorColor), "Build failed: ");

        OS::print(fmt::format("{} error{}, {} warning{}\n", diagEngine.getNumErrors(),
                              diagEngine.getNumErrors() == 1 ? "" : "s",
                              diagEngine.getNumWarnings(),
                              diagEngine.getNumWarnings() == 1 ? "" : "s"));
    }

    return succeeded;
}

} // namespace slang::driver
