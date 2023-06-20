// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/text/SourceManager.h"

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
