// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyConfigParser.h"
#include "TidyTest.h"

static TidyConfig typedefNames(std::string_view regex) {
    TidyConfig config;
    auto& c = config.getCheckConfigs();
    c.typedefRegexString = regex;
    c.typedefRegexPattern = boost::regex(c.typedefRegexString);
    return config;
}

static TidyConfig typedefNamesNoSpecialized(std::string_view regex) {
    std::string configStr = R"(Checks:
    -style-enum-name,
    -style-struct-name,
    -style-union-name
CheckConfigs:
    typedefRegexString: ")";
    configStr += regex;
    configStr += "\"\n";
    return TidyConfigParser(configStr).getConfig();
}

static TidyConfig typedefNamesDisable(std::string_view regex, std::string_view disabledChecks) {
    std::string configStr = "Checks:\n    ";
    configStr += disabledChecks;
    configStr += "\nCheckConfigs:\n    typedefRegexString: \"";
    configStr += regex;
    configStr += "\"\n";
    return TidyConfigParser(configStr).getConfig();
}

TEST_CASE("TypedefName: matching name") {
    CHECK(runCheckTest("TypedefName", "typedef logic my_type_t;", typedefNames(".*_t")));
}

TEST_CASE("TypedefName: mismatched name") {
    CHECK_FALSE(runCheckTest("TypedefName", "typedef logic my_type;", typedefNames(".*_t")));
}

TEST_CASE("TypedefName: alias of another type") {
    CHECK(runCheckTest("TypedefName", "typedef logic my_type_t; typedef my_type_t other_t;",
                       typedefNames(".*_t")));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef logic my_type_t; typedef my_type_t other;",
                             typedefNames(".*_t")));
}

TEST_CASE("TypedefName: typedef in class") {
    CHECK(runCheckTest("TypedefName", R"(
class C;
    typedef logic my_type_t;
endclass
)",
                       typedefNames(".*_t")));
}

TEST_CASE("TypedefName: forward declaration") {
    CHECK(runCheckTest("TypedefName", "typedef my_type_t;", typedefNames(".*_t")));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef my_type;", typedefNames(".*_t")));
}

TEST_CASE("TypedefName: class forward declaration") {
    CHECK(runCheckTest("TypedefName", "typedef class my_type_t;", typedefNames(".*_t")));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef class my_type;", typedefNames(".*_t")));
}

TEST_CASE("TypedefName: default regex") {
    CHECK(runCheckTest("TypedefName", "typedef logic my_type_t;"));
    CHECK(runCheckTest("TypedefName", "typedef logic my_type_2_t;"));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef logic my_type;"));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef logic My_type_t;"));
}

TEST_CASE("TypedefName: specialized checks take precedence when enabled") {
    auto config = typedefNames(".*_t");
    CHECK(runCheckTest("TypedefName", "typedef enum { RED, BLUE } color_e;", config));
    CHECK(runCheckTest("TypedefName", "typedef struct { int value; } color_s;", config));
    CHECK(runCheckTest("TypedefName", "typedef union { int value; } color_u;", config));
    CHECK(runCheckTest("TypedefName", "typedef enum color_e;", config));
    CHECK(runCheckTest("TypedefName", "typedef struct color_s;", config));
    CHECK(runCheckTest("TypedefName", "typedef union color_u;", config));
}

TEST_CASE("TypedefName: still lints non-specialized typedefs when specialized checks are enabled") {
    auto config = typedefNames(".*_t");
    CHECK_FALSE(runCheckTest("TypedefName", "typedef logic color_e;", config));
}

TEST_CASE("TypedefName: applies to enum/struct/union when specialized checks are disabled") {
    auto config = typedefNamesNoSpecialized(".*_t");
    CHECK_FALSE(runCheckTest("TypedefName", "typedef enum { RED, BLUE } color_e;", config));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef struct { int value; } color_s;", config));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef union { int value; } color_u;", config));
    CHECK(runCheckTest("TypedefName", "typedef enum { RED, BLUE } color_t;", config));
    CHECK(runCheckTest("TypedefName", "typedef struct { int value; } color_t;", config));
    CHECK(runCheckTest("TypedefName", "typedef union { int value; } color_t;", config));
    CHECK_FALSE(runCheckTest("TypedefName", "typedef enum color_e;", config));
    CHECK(runCheckTest("TypedefName", "typedef enum color_t;", config));
}

TEST_CASE("TypedefName: only enabled specialized checks take precedence") {
    auto config = typedefNamesDisable(".*_t", "-style-enum-name");
    CHECK_FALSE(runCheckTest("TypedefName", "typedef enum { RED, BLUE } color_e;", config));
    CHECK(runCheckTest("TypedefName", "typedef struct { int value; } color_s;", config));
    CHECK(runCheckTest("TypedefName", "typedef union { int value; } color_u;", config));
}
