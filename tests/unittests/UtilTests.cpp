#include "Test.h"

#include "slang/util/CommandLine.h"

TEST_CASE("Test CommandLine -- basic") {
    optional<bool> a, b, longFlag;
    optional<std::string> c;
    optional<int32_t> d;
    optional<uint64_t> ext;
    optional<double> ext2;
    optional<uint32_t> unused1;
    optional<int64_t> unused2;
    std::vector<std::string> vals;

    CommandLine cmdLine;
    cmdLine.add("-a", a, "SDF");
    cmdLine.add("-b", b, "SDF");
    cmdLine.add("-z,-y,-x,--longFlag", longFlag, "SDF");
    cmdLine.add("-c", c, "SDF", "val");
    cmdLine.add("-d", d, "SDF", "val");
    cmdLine.add("-e,--ext", ext, "SDF", "val");
    cmdLine.add("-f,--ext2", ext2, "SDF", "val");
    cmdLine.add("--biz,--baz", unused1, "SDF", "val");
    cmdLine.add("--buz,--boz", unused2, "SDF", "val");
    cmdLine.setPositional(vals, "vals");

    CHECK(cmdLine.parse("prog -a -b --longFlag=False pos1 pos2 -c asdf -d -1234 --ext=9876 "
                        "--ext2 9999.1234e12 pos3 - pos5 -- --buz --boz"sv));

    CHECK(a);
    CHECK(b);
    CHECK(longFlag);
    CHECK(c);
    CHECK(d);
    CHECK(ext);
    CHECK(ext2);
    CHECK(!unused1);
    CHECK(!unused2);

    CHECK(*a == true);
    CHECK(*b == true);
    CHECK(*longFlag == false);
    CHECK(*c == "asdf");
    CHECK(*d == -1234);
    CHECK(*ext == 9876);
    CHECK(*ext2 == 9999.1234e12);
    
    REQUIRE(vals.size() == 7);
    CHECK(vals[0] == "pos1");
    CHECK(vals[1] == "pos2");
    CHECK(vals[2] == "pos3");
    CHECK(vals[3] == "-");
    CHECK(vals[4] == "pos5");
    CHECK(vals[5] == "--buz");
    CHECK(vals[6] == "--boz");
}