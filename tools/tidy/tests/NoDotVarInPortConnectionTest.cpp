// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("NoDotVarInPortConnection: Use of dot var in module port connection") {
    auto result = runCheckTest("NoDotVarInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .rst);
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoDotVarInPortConnection: Module port connection port by port") {
    auto result = runCheckTest("NoDotVarInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .rst(rst));
endmodule
)");
    CHECK(result);
}

TEST_CASE("NoDotVarInPortConnection: Use of dot star in module port connection") {
    auto result = runCheckTest("NoDotVarInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.*);
endmodule
)");
    CHECK(result);
}
