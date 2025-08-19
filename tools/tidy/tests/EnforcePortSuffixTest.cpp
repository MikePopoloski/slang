// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("EnforcePortSuffix: Incorrect input suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    input logic a
);
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct input suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    input logic a_i
);
endmodule
)");
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Incorrect output suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    output logic a
);
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct output suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    output logic a_o
);
endmodule
)");
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Incorrect inout suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    inout logic a
);
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct inout suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    inout logic a_io
);
endmodule
)");
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Multiple suffixes for input port") {
    TidyConfig config;
    config.getCheckConfigs().inputPortSuffix = {"_a", "_b", "_c"};

    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic in_a,
    input logic in_b,
    input logic in_c
);
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Ignore some port suffixes") {
    TidyConfig config;
    config.getCheckConfigs().inputPortSuffix = {};
    config.getCheckConfigs().outputPortSuffix = {""};

    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input logic abc,
    output logic bcd
);
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Explicit ports") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input .data_i({a1, b1}),
    output .data_o({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)");
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Explicit port with incorrect suffix") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
    input .data_i({a1, b1}),
    input .data_o({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Implicit port name") {
    auto result = runCheckTest("EnforcePortSuffix", R"(
module top (
  i[31:0]
);
    output var [31:0] i;
endmodule
)");
    CHECK_FALSE(result);
}
