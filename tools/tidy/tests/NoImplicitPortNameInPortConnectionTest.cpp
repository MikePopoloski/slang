// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE(
    "NoImplicitPortNameInPortConnection: Only port name specified in module port connection") {
    auto result = runCheckTest("NoImplicitPortNameInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk, .rst(rst));
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoImplicitPortNameInPortConnection: Module port connection port by port") {
    auto result = runCheckTest("NoImplicitPortNameInPortConnection", R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .rst(rst));
endmodule
)");
    CHECK(result);
}
