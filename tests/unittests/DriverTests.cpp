// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>
#include <fstream>
#include <regex>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"

using namespace slang::driver;

static bool stdoutContains(std::string_view text) {
    return OS::capturedStdout.find(text) != std::string::npos;
}

static bool stderrContains(std::string_view text) {
    return OS::capturedStderr.find(text) != std::string::npos;
}

TEST_CASE("Driver basic") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
}

TEST_CASE("Driver invalid command line arg") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--foo=bar"};
    CHECK(!driver.parseCommandLine(2, argv));
    CHECK(stderrContains("unknown command line arg"));
}

TEST_CASE("Driver invalid compat") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=baz"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid value for compat option"));
}

TEST_CASE("Driver invalid timing") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "-TFoo"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid value for timing option"));
}

TEST_CASE("Driver invalid diagHierarchy") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--diag-hierarchy=foo"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid value for diag-hierarchy option"));
}

TEST_CASE("Driver invalid timescale") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--timescale=\"foo\""};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid value for time scale option"));
}

TEST_CASE("Driver invalid translate-off-format") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--translate-off-format=a,b,c,d",
                          "--translate-off-format=a,,c", "--translate-off-format=a,^^,c"};
    CHECK(driver.parseCommandLine(4, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid format for translate-off-format"));
}

TEST_CASE("Driver invalid include dirs") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "-Ifoo/bar/baz/", "--isystem=foo/bar/baz/"};
    CHECK(driver.parseCommandLine(3, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("warning: system include directory 'foo/bar/baz/':"));
    CHECK(stderrContains("no input files"));
}

TEST_CASE("Driver missing single-unit for inherit macros") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--libraries-inherit-macros"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("--single-unit must be set"));
}

TEST_CASE("Driver invalid source file") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "blah.sv"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("error: 'blah.sv':"));
}

TEST_CASE("Driver file preprocess") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(driver.runPreprocessor(true, false, false));

    auto output = OS::capturedStdout;
    output = std::regex_replace(output, std::regex("\r\n"), "\n");

    CHECK(output.starts_with("\nmodule m;\n"
                             "    // hello\n"
                             "    int i = 32'haa_bb??e;\n"
                             "    string s = "));

    CHECK(output.ends_with(";\n"
                           "    begin end\n"
                           "endmodule\n"
                           "\n"));
}

TEST_CASE("Driver file preprocess -- obfuscation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(driver.runPreprocessor(true, false, true, true));

    auto output = OS::capturedStdout;
    output = std::regex_replace(output, std::regex("\r\n"), "\n");

    CHECK(output.starts_with("\nmodule AOOpUHNpKPjVcKHQ;\n"
                             "    // hello\n"
                             "    int LMxOpJDziyYJoPIV = 32'haa_bb??e;\n"
                             "    string pmOPtNbMAqvklYVm = "));

    CHECK(output.ends_with(";\n"
                           "    begin end\n"
                           "endmodule\n"
                           "\n"));
}

TEST_CASE("Driver file preprocess with error") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test2.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(!driver.runPreprocessor(true, false, false));
    CHECK(stderrContains("unknown macro"));
}

TEST_CASE("Driver report macros") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    driver.reportMacros();

    CHECK(("\n" + OS::capturedStdout).starts_with(R"(
BAR `__FILE__
FOO `BAR
ID(x) x
SV_COV_ASSERTION 20
SV_COV_CHECK 3
SV_COV_ERROR -1
SV_COV_FSM_STATE 21
SV_COV_HIER 11
SV_COV_MODULE 10
SV_COV_NOCOV 0
SV_COV_OK 1
SV_COV_OVERFLOW -2
SV_COV_PARTIAL 2
SV_COV_RESET 2
SV_COV_START 0
SV_COV_STATEMENT 22
SV_COV_STOP 1
SV_COV_TOGGLE 23
__slang__ 1
)"));

    CHECK(stdoutContains("__slang_major__"));
    CHECK(stdoutContains("__slang_minor__"));
}

TEST_CASE("Driver includes depfile") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    fs::current_path(findTestDir());
    auto depfiles = driver.getIncludePaths();
    CHECK(depfiles == std::vector<fs::path>{
                          fs::current_path() / "file_defn.svh",
                      });

    CHECK(driver.serializeDepfiles(depfiles, {"target"}) == "target: file_defn.svh\n");
    CHECK(driver.serializeDepfiles(depfiles, std::nullopt) == "file_defn.svh\n");
}

TEST_CASE("Driver module depfile") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    fs::current_path(findTestDir());
    CHECK(driver.sourceLoader.getFilePaths() == std::vector<fs::path>{
                                                    fs::current_path() / "test.sv",
                                                });
    CHECK(driver.serializeDepfiles(driver.sourceLoader.getFilePaths(), {"target"}) ==
          "target: test.sv\n");
    CHECK(driver.serializeDepfiles(driver.sourceLoader.getFilePaths(), std::nullopt) ==
          "test.sv\n");
}

TEST_CASE("Driver single-unit parsing") {
    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test.sv\" \"{0}test2.sv\" --single-unit --lint-only",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());
}

TEST_CASE("Driver single-unit parsing files with no EOL") {
    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}file_with_no_eol.sv\" "
                            "\"{0}file_uses_define_in_file_with_no_eol.sv\" --single-unit",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());
}

TEST_CASE("Driver parsing with library modules") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format(
        "testfoo \"{0}test3.sv\" --libdir \"{0}\"library --libext .qv -Wno-foobar", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    CHECK(stderrContains("unknown warning option"));
    CHECK(stderrContains("foobaz"));
}

TEST_CASE("Driver invalid library module file") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "-vblah.sv"};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("error: 'blah.sv':"));
}

TEST_CASE("Driver parsing multiple input files") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test?.sv\" --single-unit --libraries-inherit-macros -v "
                            "\"{0}library/libmod.qv\"",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.reportParseDiags());
}

TEST_CASE("Driver full compilation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test.sv\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
}

TEST_CASE("Driver full compilation with defines and param overrides") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format(
        "testfoo \"{0}test4.sv\" --top=frob --allow-use-before-declare -DFOOBAR -Gbar=1",
        findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
}

TEST_CASE("Driver setting a bunch of compilation options") {
    for (auto timing : {"min", "typ", "max"}) {
        auto guard = OS::captureOutput();

        Driver driver;
        driver.addStandardArgs();

        auto args = fmt::format("testfoo \"{0}test.sv\" -T{1}", findTestDir(), timing);
        args += " --max-include-depth=4 --max-parse-depth=10 --max-lexer-errors=2";
        args += " --max-hierarchy-depth=10 --max-generate-steps=1  --max-constexpr-depth=1";
        args += " --max-constexpr-steps=2 --constexpr-backtrace-limit=4 --max-instance-array=5";
        args += " --ignore-unknown-modules --relax-enum-conversions --allow-hierarchical-const";
        args += " --allow-dup-initial-drivers --lint-only";
        args += " --color-diagnostics=false";
        args += " --timescale=10ns/10ps";

        CHECK(driver.parseCommandLine(args));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());
        CHECK(driver.runFullCompilation());
        CHECK(stdoutContains("Build succeeded"));
    }
}

TEST_CASE("Driver failed compilation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args =
        fmt::format("testfoo \"{0}test4.sv\" --allow-use-before-declare --error-limit=2 --top=baz",
                    findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stdoutContains("1 error, 1 warning"));
}

TEST_CASE("Driver command files") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo -F \"{0}cmd.f\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
}

TEST_CASE("Driver command file errors") {
    for (auto type : {"f", "F"}) {
        auto guard = OS::captureOutput();

        Driver driver;
        driver.addStandardArgs();

        auto args = fmt::format("testfoo -{} \"{}cmd2.f\"", type, findTestDir());
        CHECK(!driver.parseCommandLine(args));
        CHECK(!driver.processOptions());
    }
}

TEST_CASE("Driver unknown command file") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo -F \"asdfasdf\"", findTestDir());
    CHECK(!driver.parseCommandLine(args));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("error: command file 'asdfasdf':"));
}

TEST_CASE("Driver allow defines to be inherited to lib files") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test3.sv\" --libdir \"{0}\"library --libext .qv --top=qq "
                            "--single-unit --libraries-inherit-macros",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
}

TEST_CASE("Driver command files are processed strictly in order") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}\"test.sv -F \"{0}cmd3.f\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());

    std::vector<std::string_view> fileNames;
    for (auto buffer : driver.sourceLoader.loadSources()) {
        auto name = driver.sourceManager.getRawFileName(buffer.id);
        if (auto idx = name.find_last_of("/\\"); idx != name.npos)
            name = name.substr(idx + 1);

        fileNames.push_back(name);
    }

    CHECK(fileNames.size() == 4);
    CHECK(std::ranges::is_sorted(fileNames));
}

TEST_CASE("Driver flag --exclude-ext (multiple use)") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath1 = findTestDir() + "test.sv";
    auto filePath2 = findTestDir() + "test.vhd";
    auto filePath3 = findTestDir() + "test.e";
    const char* argv[] = {"testfoo", "--exclude-ext=vhd,e", filePath1.c_str(), filePath2.c_str(),
                          filePath3.c_str()};
    CHECK(driver.parseCommandLine(sizeof(argv) / sizeof(argv[0]), argv));
    CHECK(driver.processOptions());
}

TEST_CASE("Driver suppress warnings by path") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test5.sv\" -Weverything --suppress-warnings \"{0}\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stdoutContains("0 errors, 0 warnings"));
}

TEST_CASE("Driver suppress macro warnings by path") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format(
        "testfoo \"{0}test6.sv\" -Wwidth-trunc --suppress-macro-warnings \"{0}/nested/\"", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stdoutContains("0 errors, 0 warnings"));
}

static bool contains(std::string_view str, std::string_view value) {
    return str.find(value) != std::string_view::npos;
}

TEST_CASE("Driver library files with explicit name") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --single-unit --libraries-inherit-macros "
                            " \"-I{0}/nested\" \"-vlibfoo={0}/library/.../*.sv\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        // Ignore include files and macro buffers.
        if (sm.isMacroLoc(SourceLocation(buf, 0)) || sm.getIncludedFrom(buf))
            continue;

        auto lib = sm.getLibraryFor(buf);
        auto name = sm.getRawFileName(buf);
        if (contains(name, "test6.sv")) {
            CHECK(!lib);
        }
        else {
            REQUIRE(lib);
            CHECK(lib->name == "libfoo");
        }
    }
}

TEST_CASE("Driver load library maps") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\"", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        // Ignore include files and macro buffers.
        if (sm.isMacroLoc(SourceLocation(buf, 0)) || sm.getIncludedFrom(buf))
            continue;

        auto name = sm.getRawFileName(buf);
        if (contains(name, ".map"))
            continue;

        auto lib = sm.getLibraryFor(buf);
        REQUIRE(lib);
        if (contains(name, "libmod.qv") || contains(name, "pkg.sv") || contains(name, "other.sv")) {
            CHECK(lib->name == "libfoo");
        }
        else {
            CHECK(lib->name == "libsys");
        }
    }

    CHECK(driver.sourceLoader.getLibraryMaps().size() == 2);
}

TEST_CASE("Driver library map in compilation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\"", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stdoutContains("0 errors, 2 warnings"));
}

TEST_CASE("Driver checking for infinite command file includes") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo -F \"{0}infinite.f\"", testDir);
    CHECK(!driver.parseCommandLine(args));
    CHECK(stderrContains("error: command file "));
    CHECK(stderrContains("includes itself recursively"));
}

TEST_CASE("Driver checking for infinite library map includes") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo --libmap \"{0}infinite.map\"", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("error: library map "));
    CHECK(stderrContains("includes itself recursively"));
}

TEST_CASE("Driver separate unit listing") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test5.sv\" -C \"{0}unit.f\" -v \"lib2={0}test6.sv\"",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, false);
    CHECK(driver.reportDiagnostics(false));
    CHECK(stdoutContains("Build succeeded"));

    auto& root = compilation->getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->getSourceLibrary()->name == "work");
    CHECK(root.topInstances[0]->name == "k");

    auto units = compilation->getCompilationUnits();
    REQUIRE(units.size() == 3);
    REQUIRE(units[1]->getSourceLibrary() != nullptr);
    REQUIRE(units[2]->getSourceLibrary() != nullptr);
    CHECK(units[1]->getSourceLibrary()->name == "lib2");
    CHECK(units[2]->getSourceLibrary()->name == "mylib");

    auto defs = compilation->getDefinitions();
    auto it = std::ranges::find_if(defs, [](auto sym) {
        return sym->kind == SymbolKind::Definition && sym->name == "mod1" &&
               sym->getSourceLibrary() && sym->getSourceLibrary()->name == "mylib";
    });
    CHECK(it != defs.end());
}

TEST_CASE("Driver customize default lib name") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test5.sv\" -v \"blah={0}test6.sv\" --defaultLibName blah",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, false);
    CHECK(driver.reportDiagnostics(false));
    CHECK(stdoutContains("Build succeeded"));

    auto& root = compilation->getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->getSourceLibrary()->name == "blah");
    CHECK(root.topInstances[0]->name == "k");

    auto units = compilation->getCompilationUnits();
    REQUIRE(units.size() == 2);
    REQUIRE(units[0]->getSourceLibrary() != nullptr);
    REQUIRE(units[1]->getSourceLibrary() != nullptr);
    CHECK(units[0]->getSourceLibrary()->name == "blah");
    CHECK(units[1]->getSourceLibrary()->name == "blah");
}

TEST_CASE("Driver JSON diag output") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\" "
                            "--diag-json -",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation(true));
    CHECK(stdoutContains(R"({
    "severity": "warning",
    "message": "no top-level modules found in design",
    "optionName": "missing-top",
    "symbolPath": "\\$root "
  }
)"));
}

TEST_CASE("Driver dependency tracking and pruning") {
    auto testDir = findTestDir();

    // Test case 1: Request only moduleB as top module
    // Should return moduleB, moduleA (dependency), but not moduleC or moduleD
    {
        Driver driver;
        driver.addStandardArgs();

        auto moduleA = testDir + "dep_moduleA.sv";
        auto moduleB = testDir + "dep_moduleB.sv";
        auto moduleC = testDir + "dep_moduleC.sv";
        auto moduleD = testDir + "dep_moduleD.sv";

        const char* argv[] = {"testfoo",       "--top=moduleB", moduleA.c_str(),
                              moduleB.c_str(), moduleC.c_str(), moduleD.c_str()};

        CHECK(driver.parseCommandLine(6, argv));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());

        auto result = driver.getReferencedDeps();

        // Should find moduleB and its dependency moduleA
        CHECK(result.depTrees.size() == 2);

        // Check that we have the right modules
        bool foundA = false, foundB = false, foundC = false, foundD = false;

        for (const auto& tree : result.depTrees) {
            auto bufferIds = tree->getSourceBufferIds();
            CHECK(!bufferIds.empty());

            for (auto bufferId : bufferIds) {
                auto fileName = tree->sourceManager().getFileName(SourceLocation(bufferId, 0));
                if (fileName.find("dep_moduleA.sv") != std::string::npos)
                    foundA = true;
                else if (fileName.find("dep_moduleB.sv") != std::string::npos)
                    foundB = true;
                else if (fileName.find("dep_moduleC.sv") != std::string::npos)
                    foundC = true;
                else if (fileName.find("dep_moduleD.sv") != std::string::npos)
                    foundD = true;
            }
        }

        CHECK(foundA);  // moduleB depends on moduleA
        CHECK(foundB);  // moduleB is the top module
        CHECK(!foundC); // moduleC should be pruned (not needed for moduleB)
        CHECK(!foundD); // moduleD should be pruned (independent)

        // Should have no missing dependencies
        CHECK(result.missingNames.empty());
        CHECK(result.missingTops.empty());
    }

    // Test case 2: Request moduleC as top module
    // Should return moduleC, moduleB, moduleA (all dependencies), but not moduleD
    {
        Driver driver2;
        driver2.addStandardArgs();

        auto moduleA = testDir + "dep_moduleA.sv";
        auto moduleB = testDir + "dep_moduleB.sv";
        auto moduleC = testDir + "dep_moduleC.sv";
        auto moduleD = testDir + "dep_moduleD.sv";

        const char* argv[] = {"testfoo",       "--top=moduleC", moduleA.c_str(),
                              moduleB.c_str(), moduleC.c_str(), moduleD.c_str()};

        CHECK(driver2.parseCommandLine(6, argv));
        CHECK(driver2.processOptions());
        CHECK(driver2.parseAllSources());

        auto result2 = driver2.getReferencedDeps();

        // Should find moduleC and its dependencies (B and A)
        CHECK(result2.depTrees.size() == 3);

        bool foundA = false, foundB = false, foundC = false, foundD = false;

        for (const auto& tree : result2.depTrees) {
            auto bufferIds = tree->getSourceBufferIds();
            CHECK(!bufferIds.empty());

            for (auto bufferId : bufferIds) {
                auto fileName = tree->sourceManager().getFileName(SourceLocation(bufferId, 0));
                if (fileName.find("dep_moduleA.sv") != std::string::npos)
                    foundA = true;
                else if (fileName.find("dep_moduleB.sv") != std::string::npos)
                    foundB = true;
                else if (fileName.find("dep_moduleC.sv") != std::string::npos)
                    foundC = true;
                else if (fileName.find("dep_moduleD.sv") != std::string::npos)
                    foundD = true;
            }
        }

        CHECK(foundA);  // moduleC -> moduleB -> moduleA
        CHECK(foundB);  // moduleC -> moduleB
        CHECK(foundC);  // moduleC is the top module
        CHECK(!foundD); // moduleD should be pruned (independent)
    }

    // Test case 3: Request non-existent module
    // Should report missing top module
    {
        Driver driver3;
        driver3.addStandardArgs();

        auto moduleA = testDir + "dep_moduleA.sv";
        auto moduleB = testDir + "dep_moduleB.sv";

        const char* argv[] = {"testfoo", "--top=nonexistent", moduleA.c_str(), moduleB.c_str()};

        CHECK(driver3.parseCommandLine(4, argv));
        CHECK(driver3.processOptions());
        CHECK(driver3.parseAllSources());

        auto result3 = driver3.getReferencedDeps();

        // Should have no trees but report missing top
        CHECK(result3.depTrees.empty());
        CHECK(!result3.missingTops.empty());
        CHECK(std::find(result3.missingTops.begin(), result3.missingTops.end(), "nonexistent") !=
              result3.missingTops.end());
    }
}

TEST_CASE("DepTracker topological sort ordering") {
    auto testDir = findTestDir();

    // Test complex dependency chain with proper topological ordering
    {
        Driver driver;
        driver.addStandardArgs();

        auto leafA = testDir + "topo/topo_leafA.sv";
        auto leafB = testDir + "topo/topo_leafB.sv";
        auto mid = testDir + "topo/topo_mid.sv";
        auto top = testDir + "topo/topo_top.sv";

        const char* argv[] = {"testfoo",     "--top=top", leafA.c_str(),
                              leafB.c_str(), mid.c_str(), top.c_str()};

        CHECK(driver.parseCommandLine(6, argv));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());

        auto result = driver.getReferencedDeps();

        // Should find all 4 modules: top -> mid -> (leafA, leafB)
        CHECK(result.depTrees.size() == 4);

        // Verify topological ordering: dependencies must come before dependents
        std::vector<std::string> fileOrder;
        for (const auto& tree : result.depTrees) {
            auto bufferIds = tree->getSourceBufferIds();
            CHECK(!bufferIds.empty());

            for (auto bufferId : bufferIds) {
                auto fileName = tree->sourceManager().getFileName(SourceLocation(bufferId, 0));
                if (fileName.find("topo_leafA.sv") != std::string::npos)
                    fileOrder.push_back("leafA");
                else if (fileName.find("topo_leafB.sv") != std::string::npos)
                    fileOrder.push_back("leafB");
                else if (fileName.find("topo_mid.sv") != std::string::npos)
                    fileOrder.push_back("mid");
                else if (fileName.find("topo_top.sv") != std::string::npos)
                    fileOrder.push_back("top");
            }
        }

        // Verify ordering constraints
        auto leafAPos = std::find(fileOrder.begin(), fileOrder.end(), "leafA");
        auto leafBPos = std::find(fileOrder.begin(), fileOrder.end(), "leafB");
        auto midPos = std::find(fileOrder.begin(), fileOrder.end(), "mid");
        auto topPos = std::find(fileOrder.begin(), fileOrder.end(), "top");

        CHECK(leafAPos != fileOrder.end());
        CHECK(leafBPos != fileOrder.end());
        CHECK(midPos != fileOrder.end());
        CHECK(topPos != fileOrder.end());

        // Both leaves must come before mid
        CHECK(leafAPos < midPos);
        CHECK(leafBPos < midPos);

        // Mid must come before top
        CHECK(midPos < topPos);
    }
}

TEST_CASE("DepTracker circular dependency handling") {
    auto testDir = findTestDir();

    // Test circular dependency detection and handling
    {
        Driver driver;
        driver.addStandardArgs();

        auto cycleA = testDir + "topo/topo_cycleA.sv";
        auto cycleB = testDir + "topo/topo_cycleB.sv";

        const char* argv[] = {"testfoo", "--top=cycleA", cycleA.c_str(), cycleB.c_str()};

        CHECK(driver.parseCommandLine(4, argv));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());

        auto result = driver.getReferencedDeps();

        // Should still include both modules despite circular dependency
        CHECK(result.depTrees.size() == 2);

        bool foundCycleA = false, foundCycleB = false;

        for (const auto& tree : result.depTrees) {
            auto bufferIds = tree->getSourceBufferIds();
            CHECK(!bufferIds.empty());

            for (auto bufferId : bufferIds) {
                auto fileName = tree->sourceManager().getFileName(SourceLocation(bufferId, 0));
                if (fileName.find("topo_cycleA.sv") != std::string::npos)
                    foundCycleA = true;
                else if (fileName.find("topo_cycleB.sv") != std::string::npos)
                    foundCycleB = true;
            }
        }

        CHECK(foundCycleA);
        CHECK(foundCycleB);

        // Algorithm should handle the cycle gracefully without infinite loop
        CHECK(result.missingNames.empty());
        CHECK(result.missingTops.empty());
    }
}

TEST_CASE("DepTracker partial dependency tree") {
    auto testDir = findTestDir();

    // Test requesting only mid-level module to verify partial tree extraction
    {
        Driver driver;
        driver.addStandardArgs();

        auto leafA = testDir + "topo/topo_leafA.sv";
        auto leafB = testDir + "topo/topo_leafB.sv";
        auto mid = testDir + "topo/topo_mid.sv";
        auto top = testDir + "topo/topo_top.sv";

        const char* argv[] = {"testfoo",     "--top=mid", leafA.c_str(),
                              leafB.c_str(), mid.c_str(), top.c_str()};

        CHECK(driver.parseCommandLine(6, argv));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());

        auto result = driver.getReferencedDeps();

        // Should find 3 modules: mid -> (leafA, leafB), but NOT top
        CHECK(result.depTrees.size() == 3);

        bool foundLeafA = false, foundLeafB = false, foundMid = false, foundTop = false;

        for (const auto& tree : result.depTrees) {
            auto bufferIds = tree->getSourceBufferIds();
            CHECK(!bufferIds.empty());

            for (auto bufferId : bufferIds) {
                auto fileName = tree->sourceManager().getFileName(SourceLocation(bufferId, 0));
                if (fileName.find("topo_leafA.sv") != std::string::npos)
                    foundLeafA = true;
                else if (fileName.find("topo_leafB.sv") != std::string::npos)
                    foundLeafB = true;
                else if (fileName.find("topo_mid.sv") != std::string::npos)
                    foundMid = true;
                else if (fileName.find("topo_top.sv") != std::string::npos)
                    foundTop = true;
            }
        }

        CHECK(foundLeafA); // mid depends on leafA
        CHECK(foundLeafB); // mid depends on leafB
        CHECK(foundMid);   // mid is the requested top module
        CHECK(!foundTop);  // top should be pruned (not needed for mid)
    }
}
