// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <atomic>
#include <filesystem>
#include <fmt/core.h>
#include <fstream>

#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/WaiverManager.h"
#include "slang/driver/Driver.h"
#include "slang/text/SourceManager.h"
#include "slang/util/OS.h"

using namespace slang;
using namespace slang::driver;

namespace {

std::string getDiagName(DiagCode code) {
    SourceManager sm;
    DiagnosticEngine engine(sm);
    return std::string(engine.getOptionName(code));
}

// Each call gets a distinct filename so an aborted test cannot leave stale
// content that fools the next run.
std::filesystem::path writeWaiver(std::string_view contents) {
    static std::atomic<unsigned> counter{0};
    auto path = std::filesystem::temp_directory_path() /
                fmt::format("waiver-{}-{}.toml", OS::getpid(), counter.fetch_add(1));
    std::ofstream out(path);
    out << contents;
    return path;
}

} // namespace

TEST_CASE("Waiver scopes to file glob") {
    auto waiverPath = writeWaiver(R"(
[[waivers]]
file = "**/waivers/y.sv"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/z.sv" -Weverything --waiver-file="{1}" --color-diagnostics=false)",
        findTestDir(), waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation()); // still expect warnings to be reported

    auto captured = OS::capturedStderr;
    CHECK(captured.find("y.sv:3") == std::string::npos); // waived
    CHECK(captured.find("z.sv:3") != std::string::npos); // still reported

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Waiver scopes to diagnostic in file") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
file = "**/waivers/y.sv"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" -Weverything --waiver-file="{1}")",
                            findTestDir(), waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("width-trunc") == std::string::npos);         // waived by file+diagnostic
    CHECK(captured.find("unused variable 'b'") != std::string::npos); // other warnings remain

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Waiver applies to a single instance via hier") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
hier = "**/u_y0"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("u_y0") == std::string::npos); // first inst waived
    CHECK(captured.find("u_y1") != std::string::npos); // second inst reported
    std::filesystem::remove(waiverPath);
}

TEST_CASE("Unused waivers are summarized") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
file = "**/waivers/nonexistent.sv"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiverPath.string());

    args += " --print-unused-waivers";
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStdout;
    CHECK(captured.find("unused waiver") != std::string::npos);
    // Match the filename only — Driver's CommandLineFlags::FilePath runs
    // fs::weakly_canonical on the value, which on Windows can resolve 8.3
    // short names so the stored path text won't match waiverPath.string().
    CHECK(captured.find(waiverPath.filename().string()) != std::string::npos);

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Waiver typo is reported") {
    auto waiverPath = writeWaiver(R"(
[[waivers]]
file = "**/waivers/x.sv"
diagnostic = "non-existent"
)");

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/x.sv" --waiver-file="{1}")", findTestDir(),
                            waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("non-existent") != std::string::npos);

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Hier waiver with dot separator") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
hier = "multi_instances.u_y0"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("u_y0") == std::string::npos); // waived via dot-separator hier
    CHECK(captured.find("u_y1") != std::string::npos); // second inst still reported
    std::filesystem::remove(waiverPath);
}

TEST_CASE("Hier waiver with slash separator") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
hier = "multi_instances/u_y0"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(
        R"(testfoo "{0}waivers/y.sv" "{0}waivers/multi_instances.sv" -Wwidth-trunc --waiver-file="{1}")",
        findTestDir(), waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("u_y0") == std::string::npos); // waived via slash-separator hier
    CHECK(captured.find("u_y1") != std::string::npos); // second inst still reported
    std::filesystem::remove(waiverPath);
}

TEST_CASE("Error when both file and hier specified") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
file = "**/y.sv"
hier = "top/u_y0"
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("both") != std::string::npos);

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Error when neither file nor hier specified") {
    auto diagName = getDiagName(diag::WidthTruncate);
    auto waiverPath = writeWaiver(fmt::format(R"(
[[waivers]]
diagnostic = "{}"
)",
                                              diagName));

    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();
    auto args = fmt::format(R"(testfoo "{0}waivers/y.sv" --waiver-file="{1}")", findTestDir(),
                            waiverPath.string());

    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());

    auto captured = OS::capturedStderr;
    CHECK(captured.find("either") != std::string::npos);

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Waiver Manager - TOML loading and validation") {
    SourceManager sm;
    DiagnosticEngine engine(sm);

    // Valid file rule
    {
        auto waiverPath = writeWaiver("[[waivers]]\nfile = \"rtl/**\"\n");
        WaiverManager mgr;
        std::string errors;
        CHECK(mgr.loadFromFile(waiverPath, engine, errors));
        std::filesystem::remove(waiverPath);
    }

    // Missing waivers key
    {
        auto waiverPath = writeWaiver("invalid = true\n");
        WaiverManager mgr;
        std::string errors;
        CHECK_FALSE(mgr.loadFromFile(waiverPath, engine, errors));
        std::filesystem::remove(waiverPath);
    }

    // Missing scope (neither file nor hier)
    {
        auto waiverPath = writeWaiver("[[waivers]]\ndiagnostic = \"unused-variable\"\n");
        WaiverManager mgr;
        std::string errors;
        CHECK_FALSE(mgr.loadFromFile(waiverPath, engine, errors));
        std::filesystem::remove(waiverPath);
    }

    // Unknown key (e.g. old-format field or typo)
    {
        auto waiverPath = writeWaiver("[[waivers]]\nfile = \"rtl/**\"\nfile_glob = \"rtl/**\"\n");
        WaiverManager mgr;
        std::string errors;
        CHECK_FALSE(mgr.loadFromFile(waiverPath, engine, errors));
        CHECK(errors.find("Unknown key") != std::string::npos);
        std::filesystem::remove(waiverPath);
    }

    {
        auto waiverPath = writeWaiver("[[waivers]]\nfile = \"rtl/**\"\n"
                                      "diagnostic = \"unused-variable\"\n"
                                      "regex = \"[invalid(\"\n");
        WaiverManager mgr;
        std::string errors;
        CHECK_FALSE(mgr.loadFromFile(waiverPath, engine, errors));
        std::filesystem::remove(waiverPath);
    }

    // Unknown diagnostic option name
    {
        auto waiverPath = writeWaiver("[[waivers]]\nfile = \"rtl/**\"\n"
                                      "diagnostic = \"not-a-real-warning\"\n");
        WaiverManager mgr;
        std::string errors;
        CHECK_FALSE(mgr.loadFromFile(waiverPath, engine, errors));
        std::filesystem::remove(waiverPath);
    }
}

TEST_CASE("Hier rule on symbol-less diagnostic surfaces in unused report") {
    SourceManager sm;
    auto buffer = sm.assignText("rtl/core.sv", "logic data_bus;\n");
    DiagnosticEngine engine(sm);

    // UnknownSystemName is a parser/diag with no associated symbol.
    Diagnostic diag(diag::UnknownSystemName, SourceLocation(buffer.id, 0));
    auto diagName = engine.getOptionName(diag.code);

    auto waiverPath = writeWaiver(fmt::format("[[waivers]]\nhier = \"top/u_foo\"\n"
                                              "diagnostic = \"{}\"\n",
                                              diagName));

    WaiverManager mgr;
    std::string errors;
    REQUIRE(mgr.loadFromFile(waiverPath, engine, errors));

    CHECK_FALSE(mgr.shouldWaive(diag, diag.location, sm, engine));
    CHECK(mgr.getUnusedCount() == 1);

    auto summary = mgr.getSummary(/* showUnused */ true);
    CHECK(summary.find("has no symbol") != std::string::npos);

    std::filesystem::remove(waiverPath);
}

TEST_CASE("Waiver Manager - Apply diagnostic line regex") {
    SourceManager sm;
    auto buffer = sm.assignText("rtl/core.sv", "logic data_bus;\n");
    DiagnosticEngine engine(sm);
    Diagnostic diag(diag::UnknownSystemName, SourceLocation(buffer.id, 0));
    auto diagName = engine.getOptionName(diag.code);

    auto waiverPath = writeWaiver(fmt::format("[[waivers]]\nfile = \"**/core.sv\"\n"
                                              "diagnostic = \"{}\"\n"
                                              "regex = \"data_bus\"\n",
                                              diagName));

    WaiverManager mgr;
    std::string errors;
    REQUIRE(mgr.loadFromFile(waiverPath, engine, errors));

    CHECK(mgr.shouldWaive(diag, diag.location, sm, engine));
    CHECK(mgr.getAppliedCount() == 1);
    CHECK(mgr.getUnusedCount() == 0);

    std::filesystem::remove(waiverPath);
}
