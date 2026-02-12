// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("UnconnectedInputPort: Module with unconnected input port") {
    auto result = runCheckTest("UnconnectedInputPort", R"(
module my_module (
    input  logic a,
    input  logic b,
    input  logic c,
    output logic d,
    output logic e
);
endmodule

module top;
    logic a, b, c, d, e;

    my_module i_my_module (
        .a(a),
        .c(c),
        .d(d),
        .e(e)
    );
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("UnconnectedInputPort: Module with all input ports connected") {
    auto result = runCheckTest("UnconnectedInputPort", R"(
module my_module (
    input  logic a,
    input  logic b,
    input  logic c,
    output logic d,
    output logic e
);
endmodule

module top;
    logic a, b, c, d, e;

    my_module i_my_module (
        .a(a),
        .b(b),
        .c(c),
        .d(d),
        .e(e)
    );
endmodule
)");
    CHECK(result);
}

TEST_CASE("UnconnectedInputPort: Module with unconnected output port should pass") {
    auto result = runCheckTest("UnconnectedInputPort", R"(
module my_module (
    input  logic a,
    input  logic b,
    output logic c,
    output logic d
);
endmodule

module top;
    logic a, b, c, d;

    my_module i_my_module (
        .a(a),
        .b(b),
        .c(c)
    );
endmodule
)");
    CHECK(result);
}

TEST_CASE("UnconnectedInputPort: Module with inout port unconnected") {
    auto result = runCheckTest("UnconnectedInputPort", R"(
module my_module (
    input  logic a,
    inout  logic b,
    output logic c
);
endmodule

module top;
    logic a, b, c;

    my_module i_my_module (
        .a(a),
        .c(c)
    );
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("UnconnectedInputPort: Module with all ports connected using implicit syntax") {
    auto result = runCheckTest("UnconnectedInputPort", R"(
module my_module (
    input  logic a,
    input  logic b,
    output logic c
);
endmodule

module top;
    logic a, b, c;

    my_module i_my_module (
        .a,
        .b,
        .c
    );
endmodule
)");
    CHECK(result);
}
