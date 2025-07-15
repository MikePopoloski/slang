//------------------------------------------------------------------------------
// rewriter.cpp
// Simple tool that parses an input file and writes it back out; used
// for verifying the round-trip nature of the parse tree and for providing common rewriting
// capabilities like expanding macros, removing comments, etc.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <cstdio>
#if defined(_WIN32)
#    include <fcntl.h>
#    include <io.h>
#endif

#include <fmt/format.h>
#include <optional>

#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/util/CommandLine.h"
#include "slang/util/OS.h"

using namespace slang;
using namespace slang::syntax;
using namespace slang::parsing;

int main(int argc, char** argv) {
    OS::setupConsole();

    SLANG_TRY {
        std::optional<bool> showHelp;

        // 1-1 mapping with selected SyntaxPrinter options
        std::optional<bool> expandIncludes;
        std::optional<bool> expandMacros;
        std::optional<bool> excludeDirectives;

        // Defaulted to true in SyntaxPrinter; we should rephrase those eventually
        std::optional<bool> excludeComments;
        std::optional<bool> squashNewlines;

        std::optional<bool> includeMissing;
        std::optional<bool> includeSkipped;

        driver::Driver driver;
        driver.addStandardArgs();

        driver.cmdLine.add("-h,--help", showHelp, "Display available options");

        // Expansion options
        driver.cmdLine.add("--expand-includes", expandIncludes,
                           "Expand include directives to show included content");
        driver.cmdLine.add("--expand-macros", expandMacros,
                           "Expand macro usages to show expanded content");

        // Directive options
        driver.cmdLine.add(
            "--exclude-directives", excludeDirectives,
            "Exclude other directives in output (doesn't control include and macro directives)");

        // Trivia options
        driver.cmdLine.add("--exclude-comments", excludeComments, "Exclude comments in output");
        driver.cmdLine.add("--squash-newlines", squashNewlines,
                           "Squash adjacent newlines into one");

        // Missing/skipped node options
        driver.cmdLine.add("--include-missing", includeMissing,
                           "Include missing (auto-inserted) nodes in output");
        driver.cmdLine.add("--exclude-skipped", includeSkipped,
                           "Exclude skipped (error) nodes in output");

        if (!driver.parseCommandLine(argc, argv))
            return 1;

        auto printHelp = [&]() {
            OS::print(fmt::format("{}", driver.cmdLine.getHelpText(
                                            "SystemVerilog rewriter - by default prints the input "
                                            "tree exactly as given.")));
        };

        if (showHelp == true) {
            printHelp();
            return 0;
        }

        bool ok = driver.parseAllSources();
        if (!ok) {
            OS::printE("error: failed to parse input files\n");
            return 1;
        }

        if (driver.syntaxTrees.empty()) {
            OS::printE("error: no input file specified\n");
            printHelp();
            return 1;
        }

        // By default print the last tree given (some flag files may pass syntax trees)
        auto tree = driver.syntaxTrees.back();

        SyntaxPrinter printer(driver.sourceManager);

        printer.setIncludeDirectives(true);
        printer.setSquashNewlines(false);

        // Apply command line overrides to defaults
        if (expandIncludes == true)
            printer.setExpandIncludes(true);
        if (expandMacros == true)
            printer.setExpandMacros(true);

        if (excludeComments == true)
            printer.setIncludeComments(false);
        if (squashNewlines == true)
            printer.setSquashNewlines(true);
        if (excludeDirectives == true)
            printer.setIncludeDirectives(false);

        if (includeMissing == true)
            printer.setIncludeMissing(true);
        if (includeSkipped == true)
            printer.setIncludeSkipped(true);

        // Make sure we reproduce newlines correctly on Windows:
#if defined(_WIN32)
        _setmode(_fileno(stdout), _O_BINARY);
#endif

        printf("%s", printer.print(*tree).str().c_str());
        return 0;
    }
    SLANG_CATCH(const std::exception& e) {
        SLANG_REPORT_EXCEPTION(e, "internal compiler error (exception): {}\n");
        return 2;
    }
}
