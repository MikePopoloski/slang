// SPDX-FileCopyrightText: Jonathan Drolet
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

static TidyConfig getTidyPrefixConfig() {
    TidyConfig config;
    config.getCheckConfigs().inputPortPrefix = {"i_"};
    config.getCheckConfigs().outputPortPrefix = {"o_"};
    config.getCheckConfigs().inoutPortPrefix = {"io_"};

    return config;
}

TEST_CASE("EnforcePortPrefix: Incorrect input prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    input logic a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortPrefix: Correct input prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    input logic i_a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Incorrect output prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    output logic a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortPrefix: Correct output prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    output logic o_a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Incorrect inout prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    inout logic a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortPrefix: Correct inout prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic i_clk,
    input logic i_rst_n,

    inout logic io_a
);
endmodule
)",
                               getTidyPrefixConfig());
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Multiple prefixes for input port") {
    auto config = getTidyPrefixConfig();
    config.getCheckConfigs().inputPortPrefix = {"a_", "b_", "c_"};
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic a_in,
    input logic b_in,
    input logic c_in
);
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Ignore some port prefixes") {
    auto config = getTidyPrefixConfig();
    config.getCheckConfigs().inputPortPrefix = {};
    config.getCheckConfigs().outputPortPrefix = {""};
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input logic abc,
    output logic bcd
);
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Explicit ports") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input .i_data({a1, b1}),
    output .o_data({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)",
                               getTidyPrefixConfig());
    CHECK(result);
}

TEST_CASE("EnforcePortPrefix: Explicit port with incorrect prefix") {
    auto result = runCheckTest("EnforcePortPrefix", R"(
module top (
    input .i_data({a1, b1}),
    input .o_data({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)",
                               getTidyPrefixConfig());
    CHECK_FALSE(result);
}
