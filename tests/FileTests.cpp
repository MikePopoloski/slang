#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

static const char RelativeTestPath[] = "../../../tests/data/include.svh";

TEST_CASE("Read source", "[files]") {
	SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(RelativeTestPath);

    CHECK(!manager.readSource("X:\\nonsense.txt"));

	auto file = manager.readSource(testPath);
    REQUIRE(file);
    CHECK(file->data.count() > 0);
}

TEST_CASE("Read header (absolute)", "[files]") {
	SourceManager manager;
    std::string testPath = manager.makeAbsolutePath(RelativeTestPath);

    // check load failure
    CHECK(manager.readHeader("X:\\nonsense.txt", FileID(), false) == nullptr);

    // successful load
    SourceBuffer* buffer = manager.readHeader(testPath, FileID(), false);
    REQUIRE(buffer);
    CHECK(!buffer->data.empty());
    CHECK(buffer->id);

    // next load should be cached
    FileID id1 = buffer->id;
	buffer = manager.readHeader(testPath, FileID(), false);
    REQUIRE(buffer);
    CHECK(!buffer->data.empty());
    CHECK(buffer->id == id1);
}

TEST_CASE("Read header (relative)", "[files]") {
	SourceManager manager;

    // relative to nothing should never return anything
    CHECK(!manager.readHeader("relative", FileID(), false));

    // get a file ID to load relative to
	SourceBuffer* buffer1 = manager.readHeader(manager.makeAbsolutePath(RelativeTestPath), FileID(), false);
    REQUIRE(buffer1);
    REQUIRE(buffer1->id);

    // reading the same header by name should return the same ID
	SourceBuffer* buffer2 = manager.readHeader("include.svh", buffer1->id, false);
    REQUIRE(buffer2);
    CHECK(buffer2->id == buffer1->id);

    // should be able to load relative
	buffer2 = manager.readHeader("nested/file.svh", buffer1->id, false);
    REQUIRE(buffer2);
    CHECK(!buffer2->data.empty());

    // load another level of relative
    CHECK(manager.readHeader("nested_local.svh", buffer2->id, false));
}

TEST_CASE("Read header (include dirs)", "[files]") {
    SourceManager manager;
	manager.addSystemDirectory(manager.makeAbsolutePath("../../../tests/data/"));

    SourceBuffer* buffer = manager.readHeader("include.svh", FileID(),true);
    REQUIRE(buffer);

	manager.addUserDirectory(manager.makeAbsolutePath("../../../tests/data/nested"));
	buffer = manager.readHeader("../infinite_chain.svh", buffer->id, false);
    CHECK(buffer);
}

}