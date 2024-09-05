// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fstream>

#include "slang/text/Glob.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

std::string getTestInclude() {
    return findTestDir() + "/include.svh";
}

TEST_CASE("Read source") {
    SourceManager manager;
    std::string testPath = getTestInclude();

    CHECK(!manager.readSource("X:\\nonsense.txt", /* library */ nullptr));

    auto file = manager.readSource(testPath, /* library */ nullptr);
    REQUIRE(file);
    CHECK(file->data.length() > 0);
}

TEST_CASE("Read header (absolute)") {
    SourceManager manager;
    std::string testPath = getTestInclude();

    // check load failure
    auto result = manager.readHeader("X:\\nonsense.txt", SourceLocation(), nullptr, false, {});
    CHECK(!result);
    CHECK(result.error() == std::errc::no_such_file_or_directory);

    // successful load
    auto buffer1 = manager.readHeader(testPath, SourceLocation(), nullptr, false, {});
    REQUIRE(buffer1);
    CHECK(!buffer1->data.empty());

    // next load should be cached
    auto buffer2 = manager.readHeader(testPath, SourceLocation(), nullptr, false, {});
    REQUIRE(buffer2);
    CHECK(!buffer2->data.empty());
    CHECK(buffer1->data.data() == buffer2->data.data());
}

TEST_CASE("Read header (relative)") {
    SourceManager manager;

    // relative to nothing should never return anything
    auto result = manager.readHeader("relative", SourceLocation(), nullptr, false, {});
    CHECK(!result);
    CHECK(result.error() == std::errc::no_such_file_or_directory);

    // get a file ID to load relative to
    auto buffer1 = manager.readHeader(getTestInclude(), SourceLocation(), nullptr, false, {});
    REQUIRE(buffer1);

    // reading the same header by name should return the same data pointer
    auto buffer2 = manager.readHeader("include.svh", SourceLocation(buffer1->id, 0), nullptr, false,
                                      {});
    CHECK(buffer2->data.data() == buffer1->data.data());

    // should be able to load relative
    buffer2 = manager.readHeader("nested/file.svh", SourceLocation(buffer1->id, 0), nullptr, false,
                                 {});
    REQUIRE(buffer2);
    CHECK(!buffer2->data.empty());

    // load another level of relative
    CHECK(
        manager.readHeader("nested_local.svh", SourceLocation(buffer2->id, 0), nullptr, false, {}));
}

TEST_CASE("Read header (include dirs)") {
    SourceManager manager;
    CHECK(!manager.addSystemDirectories(findTestDir()));

    auto buffer = manager.readHeader("include.svh", SourceLocation(), nullptr, true, {});
    REQUIRE(buffer);

    CHECK(!manager.addUserDirectories(findTestDir() + "/nested"));
    buffer = manager.readHeader("../infinite_chain.svh", SourceLocation(buffer->id, 0), nullptr,
                                false, {});
    CHECK(buffer);
}

TEST_CASE("Read header (dev/null)") {
    if (fs::exists("/dev/null")) {
        SourceManager manager;
        auto buffer = manager.readHeader("/dev/null", SourceLocation(), nullptr, true, {});
        CHECK(buffer);
    }
}

static void globAndCheck(const fs::path& basePath, std::string_view pattern, GlobMode mode,
                         GlobRank expectedRank, std::error_code expectedEc,
                         std::initializer_list<const char*> expected) {
    SmallVector<fs::path> results;
    std::error_code ec;
    auto rank = svGlob(basePath, pattern, mode, results, /* expandEnvVars */ true, ec);

    CHECK(rank == expectedRank);
    CHECK(results.size() == expected.size());

    if (ec != expectedEc && ec.default_error_condition() != expectedEc)
        FAIL_CHECK(ec.message() << " != " << expectedEc.message());

    for (auto str : expected) {
        auto it = std::ranges::find_if(results, [str, mode](auto& item) {
            return item.has_filename() ? item.filename() == str
                                       : item.parent_path().filename() == str;
        });
        if (it == results.end()) {
            FAIL_CHECK(str << " is not found in results for " << pattern);
        }
    }

    for (auto& path : results) {
        if (mode == GlobMode::Files)
            CHECK(fs::is_regular_file(path));
        else
            CHECK(fs::is_directory(path));
    }
}

TEST_CASE("File globbing") {
    auto testDir = findTestDir();
    globAndCheck(testDir, "*st?.sv", GlobMode::Files, GlobRank::WildcardName, {},
                 {"test2.sv", "test3.sv", "test4.sv", "test5.sv", "test6.sv"});
    globAndCheck(testDir, "system", GlobMode::Files, GlobRank::ExactPath,
                 make_error_code(std::errc::is_a_directory), {});
    globAndCheck(testDir, "system/", GlobMode::Files, GlobRank::Directory, {},
                 {"system.svh", "system.map"});
    globAndCheck(testDir, ".../f*.svh", GlobMode::Files, GlobRank::WildcardName, {},
                 {"file.svh", "file_defn.svh", "file_uses_defn.svh"});
    globAndCheck(testDir, "*ste*/", GlobMode::Files, GlobRank::Directory, {},
                 {"file.svh", "macro.svh", "nested_local.svh", "system.svh", "system.map"});
    globAndCheck(testDir, testDir + "/library/pkg.sv", GlobMode::Files, GlobRank::ExactPath, {},
                 {"pkg.sv"});
    globAndCheck(testDir, testDir + "/li?ra?y/pkg.sv", GlobMode::Files, GlobRank::SimpleName, {},
                 {"pkg.sv"});
    globAndCheck(testDir, testDir + ".../pkg.sv", GlobMode::Files, GlobRank::SimpleName, {},
                 {"pkg.sv"});
    globAndCheck(testDir, "*??blah", GlobMode::Files, GlobRank::WildcardName, {}, {});
    globAndCheck(testDir, "blah", GlobMode::Files, GlobRank::ExactPath,
                 make_error_code(std::errc::no_such_file_or_directory), {});

    putenv((char*)"BAR#=cmd");
    globAndCheck(testDir, "*${BAR#}.f", GlobMode::Files, GlobRank::WildcardName, {}, {"cmd.f"});
}

TEST_CASE("Directory globbing") {
    auto testDir = findTestDir();
    globAndCheck(testDir, "*st?.sv", GlobMode::Directories, GlobRank::WildcardName, {}, {});
    globAndCheck(testDir, "system", GlobMode::Directories, GlobRank::ExactPath, {}, {"system"});
    globAndCheck(testDir, "system/", GlobMode::Directories, GlobRank::ExactPath, {}, {"system"});
    globAndCheck(testDir, ".../", GlobMode::Directories, GlobRank::Directory, {},
                 {"library", "nested", "system", "data", "libtest"});
    globAndCheck(testDir, testDir + "/library/pkg.sv", GlobMode::Directories, GlobRank::ExactPath,
                 make_error_code(std::errc::not_a_directory), {});
}

TEST_CASE("File glob infinite recursion") {
    std::error_code ec;
    auto p = fs::temp_directory_path(ec);
    fs::current_path(p, ec);
    fs::create_directories("sandbox/a/b/c", ec);
    fs::create_directories("sandbox/a/b/d/e", ec);
    std::ofstream("sandbox/a/b/file1.txt");
    fs::create_directory_symlink(fs::absolute("sandbox/a", ec), "sandbox/a/b/c/syma", ec);

    globAndCheck({}, "sandbox/...", GlobMode::Files, GlobRank::Directory, {}, {"file1.txt"});

    fs::remove_all("sandbox", ec);
}

TEST_CASE("In-memory glob matching") {
    CHECK(svGlobMatches("foo/bar/baz.txt", "foo/bar/*.txt"));
    CHECK(svGlobMatches("foo/bar/baz.txt", "foo/bar/"));
    CHECK(!svGlobMatches("foo/bar/baz.txt", "foo/bar/*.dat"));
    CHECK(!svGlobMatches("foo/bar/baz.txt", "foo/...bat.txt"));
    CHECK(svGlobMatches("foo/bar/baz.txt", "...baz.txt"));
}
