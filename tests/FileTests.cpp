#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

static const char RelativeTestPath[] = "../../../tests/data/include.svh";

TEST_CASE("File tracking", "[files]") {
	SourceManager manager;
    FileID id1 = manager.track("stuff.txt");
    FileID id2 = manager.track("otherstuff.txt");
    FileID id3 = manager.track("stuff.txt");

    CHECK(id1 != id2);
    CHECK(id1 == id3);
}

TEST_CASE("Read source", "[files]") {
	SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(RelativeTestPath);

    SourceFile file;
    CHECK(!manager.readSource("X:\\nonsense.txt", file));
    CHECK(manager.readSource(testPath, file));
    CHECK(file.buffer.count() > 0);
}

TEST_CASE("Read header (absolute)", "[files]") {
	SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(RelativeTestPath);

    // check load failure
    CHECK(manager.readHeader(FileID(), "X:\\nonsense.txt", false) == nullptr);

    // successful load
    SourceFile* file = manager.readHeader(FileID(), testPath, false);
    REQUIRE(file);
    CHECK(!file->buffer.empty());
    CHECK(file->id);

    // next load should be cached
    FileID id1 = file->id;
    file = manager.readHeader(FileID(), testPath, false);
    REQUIRE(file);
    CHECK(!file->buffer.empty());
    CHECK(file->id == id1);
}

TEST_CASE("Read header (relative)", "[files]") {
	SourceManager manager;

    // relative to nothing should never return anything
    CHECK(!manager.readHeader(FileID(), "relative", false));

    // get a file ID to load relative to
    SourceFile* file1 = manager.readHeader(FileID(), manager.makeAbsolutePath(RelativeTestPath), false);
    REQUIRE(file1);
    REQUIRE(file1->id);

    // reading the same header by name should return the same ID
    SourceFile* file2 = manager.readHeader(file1->id, "include.svh", false);
    REQUIRE(file2);
    CHECK(file2->id == file1->id);

    // should be able to load relative
    file2 = manager.readHeader(file1->id, "nested/file.svh", false);
    REQUIRE(file2);
    CHECK(!file2->buffer.empty());

    // load another level of relative
    CHECK(manager.readHeader(file2->id, "nested_local.svh", false));
}

TEST_CASE("Read header (include dirs)", "[files]") {
    SourceManager manager;
	manager.addSystemDirectory(manager.makeAbsolutePath("../../../tests/data/"));

    SourceFile* file = manager.readHeader(FileID(), "include.svh", true);
    REQUIRE(file);

	manager.addUserDirectory(manager.makeAbsolutePath("../../../tests/data/nested"));
    file = manager.readHeader(file->id, "../infinite_chain.svh", false);
    CHECK(file);
}

}