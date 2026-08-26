// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

static TidyConfig unionNames(std::string_view regex) {
    TidyConfig config;
    auto& c = config.getCheckConfigs();
    c.unionRegexString = regex;
    c.unionRegexPattern = boost::regex(c.unionRegexString);
    return config;
}

TEST_CASE("UnionName: matching name") {
    CHECK(runCheckTest("UnionName", "typedef union { int value; } color_u;", unionNames(".*_u")));
}

TEST_CASE("UnionName: mismatched name") {
    CHECK_FALSE(
        runCheckTest("UnionName", "typedef union { int value; } color_t;", unionNames(".*_u")));
}

TEST_CASE("UnionName: ignores non-union typedefs") {
    CHECK(runCheckTest("UnionName", "typedef struct { int value; } color_t;", unionNames(".*_u")));
}

TEST_CASE("UnionName: tagged union in class") {
    CHECK(runCheckTest("UnionName", R"(
class C;
    typedef union tagged { int value; } color_u;
endclass
)",
                       unionNames(".*_u")));
}

TEST_CASE("UnionName: forward declaration") {
    CHECK(runCheckTest("UnionName", "typedef union color_u;", unionNames(".*_u")));
    CHECK_FALSE(runCheckTest("UnionName", "typedef union color_t;", unionNames(".*_u")));
}

TEST_CASE("UnionName: default regex") {
    CHECK(runCheckTest("UnionName", "typedef union { int value; } color_t;"));
    CHECK(runCheckTest("UnionName", "typedef union { int value; } color_mode_2_t;"));
    CHECK_FALSE(runCheckTest("UnionName", "typedef union { int value; } color_u;"));
    CHECK_FALSE(runCheckTest("UnionName", "typedef union { int value; } Color_t;"));
}
