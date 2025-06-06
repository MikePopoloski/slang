// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("OnlyAssignedOnReset: Only assigned on reset") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic a, b;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            a <= '0;
            b <= 1'b1;
        end else begin
            a <= 1'b1;
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("OnlyAssignedOnReset: Register always assigned") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic a, b;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            a <= '0;
        end else begin
            a <= 1'b1;
            b <= 1'b1;
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("OnlyAssignedOnReset: Register always assigned outside if reset block") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic a, b;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            a <= '0;
            b <= 1'b1;
        end else begin
            a <= 1'b1;
        end
        b <= 1'b1;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("OnlyAssignedOnReset: Array always assigned") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic push, ptr;
    logic [2:0] data;
    logic [4:0][2:0] fifo;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            fifo <= '0;
        end
        else if (push) begin
            for (int i = 0; i <= 4; i++) begin
                if (ptr == i) fifo[i] <= data;
            end
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("OnlyAssignedOnReset: Array only assigned on reset") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic push, ptr;
    logic [2:0] data;
    logic [4:0][2:0] fifo;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            fifo <= '0;
        end
        else if (push) begin
            for (int i = 0; i <= 4; i++) begin
            end
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("OnlyAssignedOnReset: Struct always assigned") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    struct {
        logic a;
        logic b;
        logic c;
    } data;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            data.a <= 1'b0;
            data.b <= 1'b0;
            data.c <= 1'b0;
        end
        else begin
            data.a <= 1'b1;
        end
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("OnlyAssignedOnReset: Struct only assigned on reset") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    struct {
        logic a;
        logic b;
        logic c;
    } data;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            data.a <= 1'b0;
            data.b <= 1'b0;
            data.c <= 1'b0;
        end
        else begin
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("OnlyAssignedOnReset: Struct only assigned on reset, reset signal inversed") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    struct {
        logic a;
        logic b;
        logic c;
    } data;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (rst_ni) begin
        end
        else begin
            data.a <= 1'b0;
            data.b <= 1'b0;
            data.c <= 1'b0;
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("OnlyAssignedOnReset: Struct array with for loop in non-reset block") {
    auto result = runCheckTest("OnlyAssignedOnReset", R"(
module top;
    logic clk_i;
    logic rst_ni;
    struct {
        logic x;
        logic z;
    } k[1:0];

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            k[0].x <= 1'b1;
            k[0].z <= 1'b1;
            k[1].x <= 1'b1;
            k[1].z <= 1'b1;
        end
        else begin
            for (int i = 0; i < 2; i++) begin
                k[i].x <= 1'b0;
                k[i].z <= 1'b0;
            end
        end
    end
endmodule
)");
    CHECK(result);
}
