// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

static TidyConfig structNames(std::string_view regex) {
    TidyConfig config;
    auto& c = config.getCheckConfigs();
    c.structRegexString = regex;
    c.structRegexPattern = boost::regex(c.structRegexString);
    return config;
}

TEST_CASE("StructName: matching name") {
    CHECK(
        runCheckTest("StructName", "typedef struct { int value; } color_s;", structNames(".*_s")));
}

TEST_CASE("StructName: mismatched name") {
    CHECK_FALSE(
        runCheckTest("StructName", "typedef struct { int value; } color_t;", structNames(".*_s")));
}

TEST_CASE("StructName: ignores non-struct typedefs") {
    CHECK(runCheckTest("StructName", "typedef union { int value; } color_t;", structNames(".*_s")));
}

TEST_CASE("StructName: packed struct in class") {
    CHECK(runCheckTest("StructName", R"(
class C;
    typedef struct packed { int value; } color_s;
endclass
)",
                       structNames(".*_s")));
}

TEST_CASE("StructName: forward declaration") {
    CHECK(runCheckTest("StructName", "typedef struct color_s;", structNames(".*_s")));
    CHECK_FALSE(runCheckTest("StructName", "typedef struct color_t;", structNames(".*_s")));
}

TEST_CASE("StructName: default regex") {
    CHECK(runCheckTest("StructName", "typedef struct { int value; } color_t;"));
    CHECK(runCheckTest("StructName", "typedef struct { int value; } color_mode_2_t;"));
    CHECK_FALSE(runCheckTest("StructName", "typedef struct { int value; } color_s;"));
    CHECK_FALSE(runCheckTest("StructName", "typedef struct { int value; } Color_t;"));
}
