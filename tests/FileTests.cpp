#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

static const char RelativeTestPath[] = "../../../tests/data/include.svh";

TEST_CASE("File tracking", "[files]") {
    SourceTracker tracker;
    FileID id1 = tracker.track("stuff.txt");
    FileID id2 = tracker.track("otherstuff.txt");
    FileID id3 = tracker.track("stuff.txt");

    CHECK(id1 != id2);
    CHECK(id1 == id3);
}

TEST_CASE("Read source", "[files]") {
    SourceTracker tracker;
    std::string testPath = tracker.makeAbsolutePath(RelativeTestPath);

    SourceFile file;
    CHECK(!tracker.readSource("X:\\nonsense.txt", file));
    CHECK(tracker.readSource(testPath, file));
    CHECK(file.buffer.count() > 0);
}

TEST_CASE("Read header (absolute)", "[files]") {
    SourceTracker tracker;
    std::string testPath = tracker.makeAbsolutePath(RelativeTestPath);

    // check load failure
    CHECK(tracker.readHeader(FileID(), "X:\\nonsense.txt", false) == nullptr);

    // successful load
    SourceFile* file = tracker.readHeader(FileID(), testPath, false);
    REQUIRE(file);
    CHECK(!file->buffer.empty());
    CHECK(file->id);

    // next load should be cached
    FileID id1 = file->id;
    file = tracker.readHeader(FileID(), testPath, false);
    REQUIRE(file);
    CHECK(!file->buffer.empty());
    CHECK(file->id == id1);
}

TEST_CASE("Read header (relative)", "[files]") {
    SourceTracker tracker;

    // relative to nothing should never return anything
    CHECK(!tracker.readHeader(FileID(), "relative", false));

    // get a file ID to load relative to
    SourceFile* file1 = tracker.readHeader(FileID(), tracker.makeAbsolutePath(RelativeTestPath), false);
    REQUIRE(file1);
    REQUIRE(file1->id);

    // reading the same header by name should return the same ID
    SourceFile* file2 = tracker.readHeader(file1->id, "include.svh", false);
    REQUIRE(file2);
    CHECK(file2->id == file1->id);

    // should be able to load relative
    file2 = tracker.readHeader(file1->id, "nested/file.svh", false);
    REQUIRE(file2);
    CHECK(!file2->buffer.empty());

    // load another level of relative
    CHECK(tracker.readHeader(file2->id, "nested_local.svh", false));
}

TEST_CASE("Read header (include dirs)", "[files]") {
    SourceTracker tracker;
    tracker.addSystemDirectory(tracker.makeAbsolutePath("../../../tests/data/"));

    SourceFile* file = tracker.readHeader(FileID(), "include.svh", true);
    REQUIRE(file);

    tracker.addUserDirectory(tracker.makeAbsolutePath("../../../tests/data/nested"));
    file = tracker.readHeader(file->id, "../infinite_chain.svh", false);
    CHECK(file);
}

}