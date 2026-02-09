// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("LoopBeforeResetCheck: Loop with reset check inside - should fail") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] a [0:3]
);
    logic [7:0] flop [0:3];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        for (int unsigned i = 0; i < 4; ++i) begin
            if (~rst_ni) begin
                flop[i] <= '0;
            end else begin
                flop[i] <= a[i];
            end
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("LoopBeforeResetCheck: Reset check before loop - should pass") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] a [0:3]
);
    logic [7:0] flop [0:3];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            for (int unsigned i = 0; i < 4; ++i) begin
                flop[i] <= '0;
            end
        end else begin
            for (int unsigned i = 0; i < 4; ++i) begin
                flop[i] <= a[i];
            end
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("LoopBeforeResetCheck: Loop without reset check - should pass") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic [7:0] a [0:3]
);
    logic [7:0] flop [0:3];

    always_ff @(posedge clk_i) begin
        for (int unsigned i = 0; i < 4; ++i) begin
            flop[i] <= a[i];
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("LoopBeforeResetCheck: Non-loop code with reset - should pass") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic a
);
    logic flop;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            flop <= '0;
        end else begin
            flop <= a;
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("LoopBeforeResetCheck: Nested loops with reset inside - should fail") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] a [0:1][0:1]
);
    logic [7:0] flop [0:1][0:1];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        for (int unsigned i = 0; i < 2; ++i) begin
            for (int unsigned j = 0; j < 2; ++j) begin
                if (~rst_ni) begin
                    flop[i][j] <= '0;
                end else begin
                    flop[i][j] <= a[i][j];
                end
            end
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("LoopBeforeResetCheck: Loop inside reset branch - should pass") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] a [0:3]
);
    logic [7:0] flop [0:3];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            for (int unsigned i = 0; i < 4; ++i) begin
                flop[i] <= '0;
            end
        end else begin
            flop[0] <= a[0];
            flop[1] <= a[1];
            flop[2] <= a[2];
            flop[3] <= a[3];
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("LoopBeforeResetCheck: Loop with no reset in sensitivity list - should pass") {
    auto result = runCheckTest("LoopBeforeResetCheck", R"(
module top (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] a [0:3]
);
    logic [7:0] flop [0:3];

    // This always_ff has NO reset in sensitivity list, so the check should not apply
    // even though there's a reset check inside the loop
    always_ff @(posedge clk_i) begin
        for (int unsigned i = 0; i < 4; ++i) begin
            if (~rst_ni) begin
                flop[i] <= '0;
            end else begin
                flop[i] <= a[i];
            end
        end
    end
endmodule
)");
    CHECK(result);
}
