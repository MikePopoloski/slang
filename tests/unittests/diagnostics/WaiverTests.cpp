// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>

#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/WaiverManager.h"
#include "slang/driver/Driver.h"
#include "slang/text/SourceManager.h"
#include "slang/util/OS.h"

using namespace slang;
using namespace slang::driver;

TEST_CASE("Waiver scopes to file glob") {
    TempFile waiver(R"(
[[waivers]]
file = "**/waivers/y.sv"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/z.sv" -Weverything --waiver-file="{1}" --color-diagnostics=false)",
        findTestDir(), waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation()); // still expect warnings to be reported

    auto captured = OS::capturedStderr;
    CHECK(!contains(captured, "y.sv:3")); // waived
    CHECK(contains(captured, "z.sv:3"));  // still reported
}

TEST_CASE("Waiver scopes to diagnostic in file") {
    TempFile waiver(R"(
[[waivers]]
file = "**/waivers/y.sv"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" -Weverything --waiver-file="{1}")",
                            findTestDir(), waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(!contains(captured, "width-trunc"));        // waived by file+diagnostic
    CHECK(contains(captured, "unused variable 'b'")); // other warnings remain
}

TEST_CASE("Waiver applies to a single instance via hier") {
    TempFile waiver(R"(
[[waivers]]
hier = "**/u_y0"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(!contains(captured, "u_y0")); // first inst waived
    CHECK(contains(captured, "u_y1"));  // second inst reported
}

TEST_CASE("Unused waivers are summarized") {
    TempFile waiver(R"(
[[waivers]]
file = "**/waivers/nonexistent.sv"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiver.path.string());

    args += " --print-unused-waivers";
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStdout;
    CHECK(contains(captured, "unused waiver"));
    // Match the filename only - Driver's CommandLineFlags::FilePath runs
    // fs::weakly_canonical on the value, which on Windows can resolve 8.3
    // short names so the stored path text won't match waiver.path.string().
    CHECK(contains(captured, waiver.path.filename().string()));
}

TEST_CASE("Waiver typo is reported") {
    TempFile waiver(R"(
[[waivers]]
file = "**/waivers/x.sv"
diagnostic = "non-existent"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/x.sv" --waiver-file="{1}")", findTestDir(),
                            waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(contains(captured, "non-existent"));
}

TEST_CASE("Hier waiver with dot separator") {
    TempFile waiver(R"(
[[waivers]]
hier = "multi_instances.u_y0"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(!contains(captured, "u_y0")); // waived via dot-separator hier
    CHECK(contains(captured, "u_y1"));  // second inst still reported
}

TEST_CASE("Hier waiver with slash separator") {
    TempFile waiver(R"(
[[waivers]]
hier = "multi_instances/u_y0"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(!contains(captured, "u_y0")); // waived via slash-separator hier
    CHECK(contains(captured, "u_y1"));  // second inst still reported
}

TEST_CASE("Error when both file and hier specified") {
    TempFile waiver(R"(
[[waivers]]
file = "**/y.sv"
hier = "top/u_y0"
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(contains(captured, "both"));
}

TEST_CASE("Error when neither file nor hier specified") {
    TempFile waiver(R"(
[[waivers]]
diagnostic = "width-trunc"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiver.path.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(contains(captured, "either"));
}

TEST_CASE("Waiver Manager - TOML loading and validation") {
    SourceManager sm;
    DiagnosticEngine engine(sm);

    // Valid file rule
    {
        TempFile waiver("[[waivers]]\nfile = \"rtl/**\"\n", ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(errors.empty());
    }

    // Missing waivers key
    {
        TempFile waiver("invalid = true\n", ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(contains(errors, "error: missing 'waivers' key"));
    }

    // Missing scope (neither file nor hier)
    {
        TempFile waiver("[[waivers]]\ndiagnostic = \"unused-variable\"\n", ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(contains(errors, "error: waiver entry must have either 'file' or 'hier' as scope"));
    }

    // Unknown key
    {
        TempFile waiver("[[waivers]]\nfile = \"rtl/**\"\nfile_glob = \"rtl/**\"\n", ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(contains(errors, "error: unknown key 'file_glob'"));
    }

    {
        TempFile waiver("[[waivers]]\nfile = \"rtl/**\"\n"
                        "diagnostic = \"unused-variable\"\n"
                        "regex = \"[invalid(\"\n",
                        ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(contains(errors, "error: invalid regex '[invalid('"));
    }

    // Unknown diagnostic option name
    {
        TempFile waiver("[[waivers]]\nfile = \"rtl/**\"\n"
                        "diagnostic = \"not-a-real-warning\"\n",
                        ".toml");
        WaiverManager mgr;
        auto errors = mgr.loadFromFile(waiver.path, engine);
        CHECK(contains(errors, "error: unknown diagnostic 'not-a-real-warning'"));
    }
}

TEST_CASE("Hier rule on symbol-less diagnostic surfaces in unused report") {
    SourceManager sm;
    auto buffer = sm.assignText("rtl/core.sv", "logic data_bus;\n");
    DiagnosticEngine engine(sm);

    // UnknownSystemName is a parser/diag with no associated symbol.
    Diagnostic diag(diag::UnknownSystemName, SourceLocation(buffer.id, 0));
    auto diagName = engine.getOptionName(diag.code);

    TempFile waiver(fmt::format("[[waivers]]\nhier = \"top/u_foo\"\n"
                                "diagnostic = \"{}\"\n",
                                diagName));

    WaiverManager mgr;
    auto errors = mgr.loadFromFile(waiver.path, engine);
    CHECK(errors.empty());

    CHECK_FALSE(mgr.shouldWaive(diag, diag.location, sm, engine));
    CHECK(mgr.getUnusedCount() == 1);

    auto summary = mgr.getSummary(/* showUnused */ true);
    CHECK(contains(summary, "has no symbol"));
}

TEST_CASE("Waiver Manager - Apply diagnostic line regex") {
    SourceManager sm;
    auto buffer = sm.assignText("rtl/core.sv", "logic data_bus;\n");

    DiagnosticEngine engine(sm);
    Diagnostic diag(diag::UnknownSystemName, SourceLocation(buffer.id, 0));
    auto diagName = engine.getOptionName(diag.code);

    TempFile waiver(fmt::format("[[waivers]]\nfile = \"**/core.sv\"\n"
                                "diagnostic = \"{}\"\n"
                                "regex = \"data_bus\"\n",
                                diagName));

    WaiverManager mgr;
    auto errors = mgr.loadFromFile(waiver.path, engine);
    CHECK(errors.empty());

    CHECK(mgr.shouldWaive(diag, diag.location, sm, engine));
    CHECK(mgr.getAppliedCount() == 1);
    CHECK(mgr.getUnusedCount() == 0);
}
