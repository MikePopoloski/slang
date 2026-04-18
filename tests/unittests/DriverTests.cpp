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

TEST_CASE("Driver basic dependency pruning") {
    // Test case 1: Request only moduleB as top module
    // Should return moduleB, moduleA (dependency), but not moduleC or moduleD
    Driver driver;
    auto treeA = SyntaxTree::fromText("module moduleA; endmodule\n", driver.sourceManager,
                                      "source"sv, "moduleA.sv"sv);
    auto treeB = SyntaxTree::fromText("module moduleB; moduleA a1(); endmodule\n",
                                      driver.sourceManager, "source"sv, "moduleB.sv"sv);
    auto treeC = SyntaxTree::fromText("module moduleC; moduleB b1(); endmodule\n",
                                      driver.sourceManager, "source"sv, "moduleC.sv"sv);
    auto treeD = SyntaxTree::fromText("module moduleD; /* independent */ endmodule\n",
                                      driver.sourceManager, "source"sv, "moduleD.sv"sv);

    driver.options.allDepfile = "-";
    driver.options.depfileTrim = true;
    driver.syntaxTrees.push_back(treeA);
    driver.syntaxTrees.push_back(treeB);
    driver.syntaxTrees.push_back(treeC);
    driver.syntaxTrees.push_back(treeD);

    {
        driver.options.topModules.push_back("moduleB");

        auto guard = OS::captureOutput();
        driver.optionallyWriteDepFiles();

        CHECK(OS::capturedStdout == "moduleA.sv\nmoduleB.sv\n");
        CHECK(OS::capturedStderr.empty());
    }

    // Test case 2: Request moduleC as top module
    // Should return moduleC, moduleB, moduleA (all dependencies), but not moduleD
    {
        driver.options.topModules.clear();
        driver.options.topModules.push_back("moduleC");

        auto guard = OS::captureOutput();
        driver.optionallyWriteDepFiles();

        CHECK(OS::capturedStdout == "moduleA.sv\nmoduleB.sv\nmoduleC.sv\n");
        CHECK(OS::capturedStderr.empty());
    }

    // Test case 3: just sorting, no trimming
    {
        driver.options.topModules.clear();
        driver.options.depfileTrim = false;
        driver.options.depfileSort = true;

        auto guard = OS::captureOutput();
        driver.optionallyWriteDepFiles();

        CHECK(OS::capturedStdout == "moduleA.sv\nmoduleB.sv\nmoduleC.sv\nmoduleD.sv\n");
        CHECK(OS::capturedStderr.empty());
    }

    // Test case 4: unknown top module
    {
        driver.options.topModules.clear();
        driver.options.topModules.push_back("unknownModule");
        driver.options.depfileTrim = true;

        auto guard = OS::captureOutput();
        driver.optionallyWriteDepFiles();

        CHECK(OS::capturedStdout == "");
        CHECK(OS::capturedStderr ==
              "warning: top module 'unknownModule' not found in any source file\n");
    }
}

TEST_CASE("Driver deplist circular dependency handling") {
    // Test circular dependency detection and handling
    // Create circular dependency: cycleA -> cycleB -> cycleA
    Driver driver;
    auto treeCycleA = SyntaxTree::fromText("module cycleA; cycleB cb(); endmodule\n",
                                           driver.sourceManager, "source"sv, "cycleA.sv"sv);
    auto treeCycleB = SyntaxTree::fromText("module cycleB; cycleA ca(); endmodule\n",
                                           driver.sourceManager, "source"sv, "cycleB.sv"sv);

    driver.options.allDepfile = "-";
    driver.options.depfileTrim = true;
    driver.syntaxTrees.push_back(treeCycleA);
    driver.syntaxTrees.push_back(treeCycleB);

    driver.options.topModules.push_back("cycleA");

    auto guard = OS::captureOutput();
    driver.optionallyWriteDepFiles();

    CHECK(OS::capturedStdout == "cycleB.sv\ncycleA.sv\n");
    CHECK(OS::capturedStderr.empty());
}

TEST_CASE("Driver deplist partial dependency tree") {
    // Test requesting only mid-level module to verify partial tree extraction
    // Create dependency hierarchy with extra unused module
    Driver driver;
    auto treeLeafA = SyntaxTree::fromText("module leafA; endmodule\n", driver.sourceManager,
                                          "source"sv, "leafA.sv"sv);
    auto treeLeafB = SyntaxTree::fromText("module leafB; endmodule\n", driver.sourceManager,
                                          "source"sv, "leafB.sv"sv);
    auto treeMid = SyntaxTree::fromText("module mid; leafA la(); leafB lb(); endmodule\n",
                                        driver.sourceManager, "source"sv, "mid.sv"sv);
    auto treeTop = SyntaxTree::fromText("module top; mid m(); endmodule\n", driver.sourceManager,
                                        "source"sv, "top.sv"sv);

    driver.options.allDepfile = "-";
    driver.options.depfileTrim = true;
    driver.syntaxTrees.push_back(treeLeafA);
    driver.syntaxTrees.push_back(treeLeafB);
    driver.syntaxTrees.push_back(treeMid);
    driver.syntaxTrees.push_back(treeTop);

    driver.options.topModules.push_back("mid");

    auto guard = OS::captureOutput();
    driver.optionallyWriteDepFiles();

    CHECK(OS::capturedStdout == "leafA.sv\nleafB.sv\nmid.sv\n");
    CHECK(OS::capturedStderr.empty());
}

TEST_CASE("Driver deplist missing dependencies") {
    // Test handling of missing dependencies
    // Create module that references non-existent module
    Driver driver;
    auto treeA = SyntaxTree::fromText("module moduleA; missingModule m(); endmodule\n",
                                      driver.sourceManager, "source"sv, "moduleA.sv"sv);

    driver.options.allDepfile = "-";
    driver.options.depfileTrim = true;
    driver.syntaxTrees.push_back(treeA);

    driver.options.topModules.push_back("moduleA");

    auto guard = OS::captureOutput();
    driver.optionallyWriteDepFiles();

    CHECK(OS::capturedStdout == "moduleA.sv\n");
    CHECK(OS::capturedStderr == "warning: 'missingModule' not found in any source file\n  note: "
                                "referenced in file 'moduleA.sv'\n");
}

TEST_CASE("Driver deplist missing top modules") {
    Driver driver;
    auto treeA = SyntaxTree::fromText("module moduleA; missingModule m(); endmodule\n",
                                      driver.sourceManager, "source"sv, "moduleA.sv"sv);

    driver.options.allDepfile = "-";
    driver.options.depfileTrim = true;
    driver.syntaxTrees.push_back(treeA);

    auto guard = OS::captureOutput();
    driver.optionallyWriteDepFiles();

    CHECK(OS::capturedStdout == "");
    CHECK(stderrContains("warning: using --depfile-trim with no top modules"));
}

TEST_CASE("Map keyword version option positive") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args =
        fmt::format("testfoo --map-keyword-version \"1364-2005+{0}*.v\" \"{0}systemverilog.sv\"",
                    findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, true);
    CHECK(driver.reportDiagnostics(false));
}

TEST_CASE("Map keyword version option negative") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format(
        "testfoo --map-keyword-version \"1364-2005+{0}*.v\" --map-keyword-version "
        "\"1364-2005+{0}systemverilog.sv,{0}another_systemverilog.sv\" \"{0}systemverilog.sv\"",
        findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, true);
    CHECK_FALSE(driver.reportDiagnostics(true));
}

TEST_CASE("Map keyword version wrong arguments") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format(
        "testfoo --map-keyword-version \"1364-2005+{0}*.v\" --map-keyword-version=asdf "
        "--map-keyword-version "
        "\"1364-2025+{0}systemverilog.sv,{0}another_systemverilog.sv\" \"{0}systemverilog.sv\"",
        findTestDir());
    CHECK_FALSE(driver.parseCommandLine(args));
}

TEST_CASE("Driver define-system-task command line parsing") {
    Driver driver;
    driver.addStandardArgs();

    auto args = "testfoo --define-system-task $my_task "
                "--define-system-task \"function int $my_func(output int a)\""sv;
    CHECK(driver.parseCommandLine(args));

    auto tree = SyntaxTree::fromText(
        "module m; initial begin int a; $my_task(); void'($my_func(a)); end endmodule\n",
        driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics().filter(DefaultIgnoreWarnings);
    CHECK(diags.empty());
}

TEST_CASE("Driver define-system-task any-args") {
    Driver driver;
    driver.addStandardArgs();
    CHECK(driver.parseCommandLine("testfoo --define-system-task $my_task"sv));

    auto tree = SyntaxTree::fromText("module m; initial $my_task(1, \"hello\", 3.14); endmodule\n",
                                     driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics().filter(DefaultIgnoreWarnings);
    CHECK(diags.empty());
}

TEST_CASE("Driver define-system-task typed args task") {
    Driver driver;
    driver.addStandardArgs();
    CHECK(driver.parseCommandLine(
        "testfoo --define-system-task \"task $my_task(int a, string b)\""sv));

    auto tree = SyntaxTree::fromText("module m; initial $my_task(42, \"hello\"); endmodule\n",
                                     driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics().filter(DefaultIgnoreWarnings);
    CHECK(diags.empty());
}

TEST_CASE("Driver define-system-task function with return type") {
    Driver driver;
    driver.addStandardArgs();
    CHECK(
        driver.parseCommandLine("testfoo --define-system-task \"function int $my_func(int a)\""sv));

    auto tree =
        SyntaxTree::fromText("module m; initial begin int x; x = $my_func(1); end endmodule\n",
                             driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics().filter(DefaultIgnoreWarnings);
    CHECK(diags.empty());
}

TEST_CASE("Driver define-system-task wrong arg count") {
    Driver driver;
    driver.addStandardArgs();
    CHECK(driver.parseCommandLine("testfoo --define-system-task \"  task $my_task(int a); \""sv));

    auto tree = SyntaxTree::fromText("module m; initial $my_task(1, 2); endmodule\n",
                                     driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::TooManyArguments);
}

TEST_CASE("Driver define-system-task no-args function") {
    Driver driver;
    driver.addStandardArgs();
    CHECK(driver.parseCommandLine("testfoo --define-system-task \"function $my_func\""sv));

    auto tree =
        SyntaxTree::fromText("module m; initial begin logic x; x = $my_func(); end endmodule\n",
                             driver.sourceManager, "source"sv);
    driver.syntaxTrees.push_back(tree);

    auto compilation = driver.createCompilation();
    auto diags = compilation->getAllDiagnostics().filter(DefaultIgnoreWarnings);
    CHECK(diags.empty());
}
