// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("UnusedSensitiveSignal: Unused sensitive signal in always block") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module d_ff_en
(
    input int a_i, b_i, c_i,

    output int sum_o
) ;
always @ (a_i , b_i, c_i ) begin
    sum_o = a_i + b_i ;
end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("UnusedSensitiveSignal: Unused sensitive signal in always_ff block") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module d_ff_en
(
    input logic clk_i, rst_i, en_i, c_i, d_i,

    output logic q_o
) ;
always_ff @ (posedge clk_i, posedge rst_i, c_i) begin
    if (rst_i)
        q_o <= '0;
    else if (en_i)
        q_o <= d_i;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("UnusedSensitiveSignal: All sensitive signal in always_ff block have been used") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module d_ff_en
(
    input logic clk_i, rst_i, en_i, c_i, d_i,

    output logic q_o
) ;
always_ff @ (posedge clk_i, posedge rst_i) begin
    if (rst_i)
        q_o <= '0;
    else if (en_i)
        q_o <= d_i;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("UnusedSensitiveSignal: property assertion") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module top
(
    input clk_i, foo_i
);

prop : assert property (@(posedge clk_i) foo_i);
endmodule
)");
    CHECK(result);
}

TEST_CASE(
    "UnusedSensitiveSignal: Clock signals not matching regex expression will raise a warning") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module d_ff_a_en
(
    input logic ck_a_i, rst_i, en_i, c_i, d_i,

    output logic q_o
) ;
always_ff @ (posedge ck_a_i, posedge rst_i) begin
    if (rst_i)
        q_o <= '0;
    else if (en_i)
        q_o <= d_i;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("UnusedSensitiveSignal: Clock signals matching regex expression won't raise a warning") {
    auto result = runCheckTest("UnusedSensitiveSignal", R"(
module d_ff_a_en
(
    input logic clock_a_i, rst_i, en_i, c_i, d_i,

    output logic q_o
) ;
always_ff @ (posedge clock_a_i, posedge rst_i) begin
    if (rst_i)
        q_o <= '0;
    else if (en_i)
        q_o <= d_i;
    end
endmodule

module d_ff_b_en
(
    input logic clk_b_i, rst_i, en_i, c_i, d_i,

    output logic q_o
) ;
always_ff @ (posedge clk_b_i, posedge rst_i) begin
    if (rst_i)
        q_o <= '0;
    else if (en_i)
        q_o <= d_i;
    end
endmodule
)");
    CHECK(result);
}
