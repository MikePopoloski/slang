// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

static TidyConfig names() {
    TidyConfig config;
    auto& c = config.getCheckConfigs();
    c.covergroupRegexString = "cg_.*";
    c.covergroupRegexPattern = boost::regex(c.covergroupRegexString);
    c.coverpointRegexString = "cp_.*";
    c.coverpointRegexPattern = boost::regex(c.coverpointRegexString);
    c.crossRegexString = "cross_.*";
    c.crossRegexPattern = boost::regex(c.crossRegexString);
    return config;
}

static std::string mod(std::string_view body) {
    return "module top;\nlogic a, b, clk, en;\n" + std::string(body) + "\nendmodule\n";
}

static bool cg(std::string_view body) {
    return runCheckTest("CovergroupName", mod(body), names());
}

static bool cp(std::string_view body) {
    return runCheckTest("CoverpointName", mod(body), names());
}

static bool cr(std::string_view body) {
    return runCheckTest("CrossName", mod(body), names());
}

TEST_CASE("CovergroupName: matching name") {
    CHECK(cg("covergroup cg_g; endgroup"));
}

TEST_CASE("CovergroupName: mismatched name") {
    CHECK_FALSE(cg("covergroup g; endgroup"));
}

TEST_CASE("CovergroupName: ports and clocking event") {
    CHECK(cg("covergroup cg_g(int w) @(posedge clk); endgroup"));
    CHECK_FALSE(cg("covergroup g(int w) @(posedge clk); endgroup"));
}

TEST_CASE("CovergroupName: in class") {
    CHECK(runCheckTest("CovergroupName", R"(
class C;
    covergroup cg_g; endgroup
endclass
)",
                       names()));
}

TEST_CASE("CoverpointName: unnamed") {
    CHECK_FALSE(cp("covergroup g; coverpoint a; endgroup"));
    CHECK_FALSE(cp("covergroup g; coverpoint a { bins x = {0}; } endgroup"));
}

TEST_CASE("CoverpointName: matching label") {
    CHECK(cp("covergroup g; cp_a: coverpoint a; endgroup"));
}

TEST_CASE("CoverpointName: mismatched label") {
    CHECK_FALSE(cp("covergroup g; a: coverpoint a; endgroup"));
}

TEST_CASE("CoverpointName: iff and bins") {
    CHECK(cp("covergroup g; cp_a: coverpoint a iff (en) { bins z = {0}; } endgroup"));
    CHECK_FALSE(cp("covergroup g; a: coverpoint a iff (en); endgroup"));
}

TEST_CASE("CoverpointName: typed coverpoint") {
    CHECK(cp("covergroup g; bit [7:0] cp_d: coverpoint a; endgroup"));
    CHECK_FALSE(cp("covergroup g; bit [7:0] d: coverpoint a; endgroup"));
}

TEST_CASE("CrossName: unnamed") {
    CHECK_FALSE(cr("covergroup g; cross a, b; endgroup"));
}

TEST_CASE("CrossName: matching label") {
    CHECK(cr("covergroup g; cross_ab: cross a, b; endgroup"));
}

TEST_CASE("CrossName: mismatched label") {
    CHECK_FALSE(cr("covergroup g; ab: cross a, b; endgroup"));
}

TEST_CASE("CrossName: iff and body") {
    CHECK(cr("covergroup g; cross_ab: cross a, b iff (en) { option.weight = 1; } endgroup"));
    CHECK_FALSE(cr("covergroup g; cross a, b iff (en); endgroup"));
}

TEST_CASE("Coverage names: default regex") {
    CHECK(runCheckTest("CovergroupName", mod("covergroup cg_g; endgroup")));
    CHECK_FALSE(runCheckTest("CovergroupName", mod("covergroup g; endgroup")));
    CHECK(runCheckTest("CoverpointName", mod("covergroup g; cp_a: coverpoint a; endgroup")));
    CHECK_FALSE(runCheckTest("CoverpointName", mod("covergroup g; a: coverpoint a; endgroup")));
    CHECK(runCheckTest("CrossName", mod("covergroup g; cross_ab: cross a, b; endgroup")));
    CHECK_FALSE(runCheckTest("CrossName", mod("covergroup g; ab: cross a, b; endgroup")));
}
