// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>
#include <fstream>
#include <regex>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/text/SourceManager.h"

using namespace slang::driver;

static bool stdoutContains(std::string_view text) {
    return OS::capturedStdout.find(text) != std::string::npos;
}

TEST_CASE("Driver basic") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
}

TEST_CASE("Driver valid column unit") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";

    const char* argv1[] = {"testfoo", "--diag-column-unit=byte", filePath.c_str()};
    CHECK(driver.parseCommandLine(3, argv1));
    CHECK(driver.processOptions());
    CHECK(driver.options.diagColumnUnit == ColumnUnit::Byte);

    const char* argv2[] = {"testfoo", "--diag-column-unit=display", filePath.c_str()};
    CHECK(driver.parseCommandLine(3, argv2));
    CHECK(driver.processOptions());
    CHECK(driver.options.diagColumnUnit == ColumnUnit::Display);
}

TEST_CASE("Driver file preprocess -- obfuscation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(driver.runPreprocessor(PreprocessOutputFlags::IncludeComments |
                                 PreprocessOutputFlags::ObfuscateIds |
                                 PreprocessOutputFlags::UseFixedObfuscationSeed));

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

TEST_CASE("Driver file kind tracking") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\" -v "
                            "\"{0}test5.sv\" \"{0}test6.sv\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        auto name = sm.getRawFileName(buf);
        auto kind = sm.getBufferKind(buf);
        if (contains(name, ".map"))
            CHECK(kind == SourceManager::BufferKind::LibraryMap);
        else if (contains(name, "test5.sv"))
            CHECK(kind == SourceManager::BufferKind::LibraryFile);
        else if (contains(name, "test6.sv"))
            CHECK(kind == SourceManager::BufferKind::DesignFile);
        else if (contains(name, "macro.svh"))
            CHECK(kind == SourceManager::BufferKind::IncludeFile);
    }
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
