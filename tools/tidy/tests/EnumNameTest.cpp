// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

static TidyConfig enumNames(std::string_view regex) {
    TidyConfig config;
    auto& c = config.getCheckConfigs();
    c.enumRegexString = regex;
    c.enumRegexPattern = boost::regex(c.enumRegexString);
    return config;
}

TEST_CASE("EnumName: matching name") {
    CHECK(runCheckTest("EnumName", "typedef enum { RED, BLUE } color_e;", enumNames(".*_e")));
}

TEST_CASE("EnumName: mismatched name") {
    CHECK_FALSE(runCheckTest("EnumName", "typedef enum { RED, BLUE } color_t;", enumNames(".*_e")));
}

TEST_CASE("EnumName: ignores non-enum typedefs") {
    CHECK(runCheckTest("EnumName", "typedef struct { int value; } color_t;", enumNames(".*_e")));
}

TEST_CASE("EnumName: enum in class") {
    CHECK(runCheckTest("EnumName", R"(
class C;
    typedef enum { RED, BLUE } color_e;
endclass
)",
                       enumNames(".*_e")));
}

TEST_CASE("EnumName: forward declaration") {
    CHECK(runCheckTest("EnumName", "typedef enum color_e;", enumNames(".*_e")));
    CHECK_FALSE(runCheckTest("EnumName", "typedef enum color_t;", enumNames(".*_e")));
}

TEST_CASE("EnumName: default regex") {
    CHECK(runCheckTest("EnumName", "typedef enum { RED, BLUE } color_e;"));
    CHECK(runCheckTest("EnumName", "typedef enum { RED, BLUE } color_mode_2_e;"));
    CHECK_FALSE(runCheckTest("EnumName", "typedef enum { RED, BLUE } color_t;"));
    CHECK_FALSE(runCheckTest("EnumName", "typedef enum { RED, BLUE } Color_e;"));
}
