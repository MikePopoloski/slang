// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <boost_regex.hpp>
#include <fmt/format.h>
#include <fstream>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/driver/SourceLoader.h"
#include "slang/text/SourceManager.h"
#include "slang/util/ScopeGuard.h"
#include "slang/util/ThreadPool.h"

using namespace slang::driver;

static bool stdoutContains(std::string_view text) {
    return contains(OS::capturedStdout, text);
}

TEST_CASE("Driver basic") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
}

TEST_CASE("Driver processOptions can skip input file check") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    CHECK(driver.processOptions(false));
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
    output = boost::regex_replace(output, boost::regex("\r\n"), "\n");

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

TEST_CASE("Driver tracks command file metadata") {
    auto guard = OS::captureOutput();

    TempFile fileWithDefs("-D FOO=1\n-D BAR=2\n");
    TempFile emptyFile("");
    TempFile extraFile("");

    Driver driver;
    driver.addStandardArgs();
    REQUIRE(driver.processCommandFiles(fileWithDefs.path.string(), false, false));
    REQUIRE(driver.processCommandFiles(emptyFile.path.string(), false, false));
    {
        auto guard = driver.setCurrentCommandFile(extraFile.path);
        const char* argv[] = {"testfoo", "-D", "BAZ=3"};
        REQUIRE(driver.parseCommandLine(3, argv));
    }
    const char* argv[] = {"testfoo", "-D", "NOT_ATTRIBUTED=1"};
    REQUIRE(driver.parseCommandLine(3, argv));

    std::error_code ec;
    auto expectedPath = fs::weakly_canonical(fileWithDefs.path, ec);
    REQUIRE(!ec);
    auto expectedEmptyPath = fs::weakly_canonical(emptyFile.path, ec);
    REQUIRE(!ec);
    auto expectedJsonPath = fs::weakly_canonical(extraFile.path, ec);
    REQUIRE(!ec);

    auto& commandFileMetadata = driver.getCommandFileMetadata();
    auto it = commandFileMetadata.find(expectedPath);
    REQUIRE(it != commandFileMetadata.end());
    CHECK(it->second.defines == std::vector<std::string>{"FOO=1", "BAR=2"});

    auto emptyIt = commandFileMetadata.find(expectedEmptyPath);
    REQUIRE(emptyIt != commandFileMetadata.end());
    CHECK(emptyIt->second.defines.empty());

    auto jsonIt = commandFileMetadata.find(expectedJsonPath);
    REQUIRE(jsonIt != commandFileMetadata.end());
    CHECK(jsonIt->second.defines == std::vector<std::string>{"BAZ=3"});
}

TEST_CASE("SourceLoader doesn't reload names satisfied by later worklist entries") {
    SourceManager sourceManager;

    auto top = SyntaxTree::fromText(R"(
module top;
    leaf leaf();
    mid mid();
endmodule
)",
                                    sourceManager, "", "load_tree_top.sv");

    SourceLoader::SyntaxTreeList trees;
    trees.push_back(top);

    flat_hash_map<std::string_view, SourceBuffer> buffers;
    buffers["mid"] = sourceManager.assignText("load_tree_mid.sv", R"(
module mid;
endmodule
module leaf;
endmodule
)");

    int leafLookups = 0;
    SourceLoader::loadTrees(trees,
                            [&](std::string_view name) {
                                if (name == "leaf")
                                    leafLookups++;
                                if (auto it = buffers.find(name); it != buffers.end())
                                    return it->second;
                                return SourceBuffer();
                            },
                            sourceManager, {});

    CHECK(leafLookups == 0);
    CHECK(trees.size() == 2);
}

#if defined(SLANG_USE_THREADS)
TEST_CASE("SourceLoader loads search libraries in parallel depths") {
    SourceManager sourceManager;

    auto top = SyntaxTree::fromText(R"(
module top;
    a a();
    b b();
    c c();
    d d();
endmodule
)",
                                    sourceManager, "", "load_tree_parallel_top.sv");

    SourceLoader::SyntaxTreeList trees;
    trees.push_back(top);

    flat_hash_map<std::string_view, SourceBuffer> buffers;
    buffers["a"] = sourceManager.assignText("load_tree_a.sv", "module a; e e(); endmodule");
    buffers["b"] = sourceManager.assignText("load_tree_b.sv", "module b; f f(); endmodule");
    buffers["c"] = sourceManager.assignText("load_tree_c.sv", "module c; g g(); endmodule");
    buffers["d"] = sourceManager.assignText("load_tree_d.sv", "module d; h h(); endmodule");
    buffers["e"] = sourceManager.assignText("load_tree_e.sv", "module e; endmodule");
    buffers["f"] = sourceManager.assignText("load_tree_f.sv", "module f; endmodule");
    buffers["g"] = sourceManager.assignText("load_tree_g.sv", "module g; endmodule");
    buffers["h"] = sourceManager.assignText("load_tree_h.sv", "module h; endmodule");

    ThreadPool pool(4);
    SourceLoader::loadTrees(
        trees,
        [&](std::string_view name) {
            if (auto it = buffers.find(name); it != buffers.end())
                return it->second;
            return SourceBuffer();
        },
        sourceManager, {}, {}, &pool);

    CHECK(trees.size() == 9);
}

TEST_CASE("SourceLoader skips parallel depth trees satisfied by earlier loads") {
    SourceManager sourceManager;

    auto top = SyntaxTree::fromText(R"(
module top;
    leaf leaf();
    a a();
    b b();
    mid mid();
endmodule
)",
                                    sourceManager, "", "load_tree_parallel_skip_top.sv");

    SourceLoader::SyntaxTreeList trees;
    trees.push_back(top);

    flat_hash_map<std::string_view, SourceBuffer> buffers;
    buffers["leaf"] = sourceManager.assignText("load_tree_leaf.sv", "module leaf; endmodule");
    buffers["mid"] = sourceManager.assignText("load_tree_mid.sv", R"(
module mid;
    helper helper();
endmodule
)");
    buffers["helper"] = sourceManager.assignText("load_tree_helper.sv", R"(
module helper;
endmodule
module leaf;
endmodule
)");
    buffers["a"] = sourceManager.assignText("load_tree_a.sv", "module a; endmodule");
    buffers["b"] = sourceManager.assignText("load_tree_b.sv", "module b; endmodule");

    ThreadPool pool(4);
    SourceLoader::loadTrees(
        trees,
        [&](std::string_view name) {
            if (auto it = buffers.find(name); it != buffers.end())
                return it->second;
            return SourceBuffer();
        },
        sourceManager, {}, {}, &pool);

    CHECK(trees.size() == 5);

    Compilation compilation;
    for (auto& tree : trees)
        compilation.addSyntaxTree(tree);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Driver libdir search loads parallel dependency depths") {
    auto guard = OS::captureOutput();

    std::error_code ec;
    auto root = fs::temp_directory_path(ec);
    REQUIRE(!ec);
    root /= fmt::format("slang-libdir-{}", OS::getpid());
    fs::remove_all(root, ec);
    fs::create_directories(root, ec);
    REQUIRE(!ec);
    ScopeGuard cleanup([&] { fs::remove_all(root, ec); });

    auto writeFile = [](const fs::path& path, std::string_view text) {
        std::ofstream out(path);
        REQUIRE(out.good());
        out << text;
    };

    writeFile(root / "top.sv", R"(
module top;
    a a();
    b b();
    c c();
    d d();
endmodule
)");
    writeFile(root / "a.qv", "module a; e e(); endmodule");
    writeFile(root / "b.qv", "module b; f f(); endmodule");
    writeFile(root / "c.qv", "module c; g g(); endmodule");
    writeFile(root / "d.qv", "module d; h h(); endmodule");
    writeFile(root / "e.qv", "module e; endmodule");
    writeFile(root / "f.qv", "module f; endmodule");
    writeFile(root / "g.qv", "module g; endmodule");
    writeFile(root / "h.qv", "module h; endmodule");

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{}\" --libdir \"{}\" --libext .qv --top top -j 4",
                            (root / "top.sv").string(), root.string());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());
    CHECK(driver.syntaxTrees.size() == 9);

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, true);
    CHECK(driver.reportDiagnostics(true));
}
#endif

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

TEST_CASE("Driver single-unit gives library files their own tree") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo --single-unit "
                            "\"{0}libsplit_top.sv\" \"{0}libsplit_lib.sv\" "
                            "--libmap \"{0}libsplit.map\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    REQUIRE(driver.syntaxTrees.size() == 2);

    int defaultUnits = 0, libraryUnits = 0;
    for (auto& tree : driver.syntaxTrees) {
        if (tree->isLibraryUnit)
            ++libraryUnits;
        else
            ++defaultUnits;
    }
    CHECK(defaultUnits == 1);
    CHECK(libraryUnits == 1);
}
