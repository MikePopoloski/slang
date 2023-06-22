// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

std::string getTestInclude() {
    return findTestDir() + "/include.svh";
}

TEST_CASE("Read source") {
    SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(getTestInclude());

    CHECK(!manager.readSource("X:\\nonsense.txt"));

    auto file = manager.readSource(testPath);
    REQUIRE(file);
    CHECK(file.data.length() > 0);
}

TEST_CASE("Read header (absolute)") {
    SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(getTestInclude());

    // check load failure
    CHECK(!manager.readHeader("X:\\nonsense.txt", SourceLocation(), false));

    // successful load
    SourceBuffer buffer = manager.readHeader(testPath, SourceLocation(), false);
    REQUIRE(buffer);
    CHECK(!buffer.data.empty());

    // next load should be cached
    buffer = manager.readHeader(testPath, SourceLocation(), false);
    CHECK(!buffer.data.empty());
}

TEST_CASE("Read header (relative)") {
    SourceManager manager;

    // relative to nothing should never return anything
    CHECK(!manager.readHeader("relative", SourceLocation(), false));

    // get a file ID to load relative to
    SourceBuffer buffer1 = manager.readHeader(manager.makeAbsolutePath(getTestInclude()),
                                              SourceLocation(), false);
    REQUIRE(buffer1);

    // reading the same header by name should return the same ID
    SourceBuffer buffer2 = manager.readHeader("include.svh", SourceLocation(buffer1.id, 0), false);

    // should be able to load relative
    buffer2 = manager.readHeader("nested/file.svh", SourceLocation(buffer1.id, 0), false);
    REQUIRE(buffer2);
    CHECK(!buffer2.data.empty());

    // load another level of relative
    CHECK(manager.readHeader("nested_local.svh", SourceLocation(buffer2.id, 0), false));
}

TEST_CASE("Read header (include dirs)") {
    SourceManager manager;
    CHECK(manager.addSystemDirectory(manager.makeAbsolutePath(findTestDir())));

    SourceBuffer buffer = manager.readHeader("include.svh", SourceLocation(), true);
    REQUIRE(buffer);

    CHECK(manager.addUserDirectory(manager.makeAbsolutePath(findTestDir() + "/nested")));
    buffer = manager.readHeader("../infinite_chain.svh", SourceLocation(buffer.id, 0), false);
    CHECK(buffer);
}

static void globAndCheck(const fs::path& basePath, std::string_view pattern,
                         std::initializer_list<const char*> expected) {
    SmallVector<fs::path> results;
    svGlob(basePath, pattern, results);

    CHECK(results.size() == expected.size());
    for (auto str : expected) {
        auto it = std::find_if(results.begin(), results.end(),
                               [str](auto& item) { return item.filename() == str; });
        if (it == results.end()) {
            FAIL_CHECK(str << " is not found in results for " << pattern);
        }
    }
}

TEST_CASE("File globbing") {
    auto testDir = findTestDir();
    globAndCheck(testDir, "*st?.sv", {"test2.sv", "test3.sv", "test4.sv", "test5.sv", "test6.sv"});
    globAndCheck(testDir, "system", {});
    globAndCheck(testDir, "system/", {"system.svh"});
    globAndCheck(testDir, ".../f*.svh", {"file.svh", "file_defn.svh", "file_uses_defn.svh"});
    globAndCheck(testDir, "*ste*/", {"file.svh", "macro.svh", "nested_local.svh", "system.svh"});
    globAndCheck(testDir, testDir + "/library/pkg.sv", {"pkg.sv"});
    globAndCheck(testDir, "*??blah", {});

    putenv((char*)"BAR#=cmd");
    globAndCheck(testDir, "*${BAR#}.f", {"cmd.f"});
}

TEST_CASE("Config Blocks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

config cfg1;
    localparam S = 24;

    design rtlLib.top;
    default liblist rtlLib;
    instance top.a2 liblist gateLib;
endconfig
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
