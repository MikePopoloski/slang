#include "Test.h"

std::string getTestInclude() {
    return findTestDir() + "/include.svh";
}

TEST_CASE("Read source", "[files]") {
    SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(StringRef(getTestInclude()));

    CHECK(!manager.readSource("X:\\nonsense.txt"));

    auto file = manager.readSource(StringRef(testPath));
    REQUIRE(file);
    CHECK(file.data.length() > 0);
}

TEST_CASE("Read header (absolute)", "[files]") {
    SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(StringRef(getTestInclude()));
    
    // check load failure
    CHECK(!manager.readHeader("X:\\nonsense.txt", SourceLocation(), false));
    
    // successful load
    SourceBuffer buffer = manager.readHeader(StringRef(testPath), SourceLocation(), false);
    REQUIRE(buffer);
    CHECK(!buffer.data.empty());
    
    // next load should be cached
    BufferID id1 = buffer.id;
    buffer = manager.readHeader(StringRef(testPath), SourceLocation(), false);
    CHECK(!buffer.data.empty());
}

TEST_CASE("Read header (relative)", "[files]") {
    SourceManager manager;

    // relative to nothing should never return anything
    CHECK(!manager.readHeader("relative", SourceLocation(), false));

    // get a file ID to load relative to
    SourceBuffer buffer1 = manager.readHeader(StringRef(manager.makeAbsolutePath(StringRef(getTestInclude()))), SourceLocation(), false);
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

TEST_CASE("Read header (include dirs)", "[files]") {
    SourceManager manager;
    manager.addSystemDirectory(StringRef(manager.makeAbsolutePath(StringRef(findTestDir()))));

    SourceBuffer buffer = manager.readHeader("include.svh", SourceLocation(), true);
    REQUIRE(buffer);

    manager.addUserDirectory(StringRef(manager.makeAbsolutePath(StringRef(findTestDir() + "/nested"))));
    buffer = manager.readHeader("../infinite_chain.svh", SourceLocation(buffer.id, 0), false);
    CHECK(buffer);
}