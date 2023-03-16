// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>
#include <regex>

#include "slang/driver/Driver.h"

using namespace slang::driver;

static bool stdoutContains(string_view text) {
    return OS::capturedStdout.find(text) != std::string::npos;
}

static bool stderrContains(string_view text) {
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

TEST_CASE("Driver invalid timescale") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--timescale=\"foo\""};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("invalid value for time scale option"));
}

TEST_CASE("Driver invalid include dirs") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "-Ifoo/bar/baz/", "--isystem=foo/bar/baz/"};
    CHECK(driver.parseCommandLine(3, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("does not exist"));
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
    CHECK(!driver.parseCommandLine(2, argv));
    CHECK(!driver.processOptions());
    CHECK(stderrContains("no such file"));
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

    CHECK(startsWith(output, "\nmodule m;\n"
                             "    // hello\n"
                             "    int i = 32'haa_bb??e;\n"
                             "    string s = "));

    CHECK(endsWith(output, ";\n"
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

    CHECK(startsWith(output, "\nmodule ykyD0R1TWLDra6jk;\n"
                             "    // hello\n"
                             "    int N65udx39eEabGtIV = 32'haa_bb??e;\n"
                             "    string TKs9hBr80Qx0xQD8 = "));

    CHECK(endsWith(output, ";\n"
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

    CHECK("\n" + OS::capturedStdout == R"(
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
__slang_major__ 2
__slang_minor__ 0
)");
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
    CHECK(driver.processOptions());
    CHECK(!driver.parseAllSources());
    CHECK(stderrContains("no such file"));
}

TEST_CASE("Driver full compilation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test.sv\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));
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

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));
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
        args += " --allow-dup-initial-drivers --strict-driver-checking --lint-only";
        args += " --color-diagnostics=false";
        args += " --timescale=10ns/10ps";

        CHECK(driver.parseCommandLine(args));
        CHECK(driver.processOptions());
        CHECK(driver.parseAllSources());

        auto compilation = driver.createCompilation();
        CHECK(driver.reportCompilation(*compilation, false));
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

    auto compilation = driver.createCompilation();
    CHECK(!driver.reportCompilation(*compilation, false));
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

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));
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
    CHECK(stderrContains("no such file or directory"));
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

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));
    CHECK(stdoutContains("Build succeeded"));
}

TEST_CASE("Driver command files are processed strictly in order") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}\"test.sv -F \"{0}cmd3.f\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());

    std::vector<string_view> fileNames;
    for (auto buffer : driver.buffers) {
        auto name = driver.sourceManager.getRawFileName(buffer.id);
        if (auto idx = name.find_last_of("/\\"); idx != name.npos)
            name = name.substr(idx + 1);

        fileNames.push_back(name);
    }

    CHECK(fileNames.size() == 4);
    CHECK(std::is_sorted(fileNames.begin(), fileNames.end()));
}

TEST_CASE("Driver flag --exclude-ext (multiple use)") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath1 = findTestDir() + "test.sv";
    auto filePath2 = findTestDir() + "test.vhd";
    auto filePath3 = findTestDir() + "test.e";
    const char* argv[] = {
        "testfoo",         "--exclude-ext",  "vhd", "--exclude-ext", "e", filePath1.c_str(),
        filePath2.c_str(), filePath3.c_str()};
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

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stdoutContains("0 errors, 0 warnings"));
}
