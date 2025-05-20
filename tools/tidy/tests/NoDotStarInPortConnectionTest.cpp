// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("NoDotStarInPortConnection: Use of dot star in module port connection") {
    auto result = runCheckTest("NoDotStarInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .*);
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoDotStarInPortConnection: Module port connection port by port") {
    auto result = runCheckTest("NoDotStarInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk, .rst(rst));
endmodule
)");
    CHECK(result);
}
