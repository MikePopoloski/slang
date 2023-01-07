//------------------------------------------------------------------------------
//! @file OnlyAssignedOnResetTest.h
//! @brief Test for the OnlyAssignedOnReset check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("OnlyAssignedOnReset: Only assigned on reset") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    logic a, b;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            a <= '0;
            b <= 1'b1;
        end else begin
            a <= 1'b1;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == false);
}

TEST_CASE("OnlyAssignedOnReset: Register always assigned") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    logic a, b;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            a <= '0;
        end else begin
            a <= 1'b1;
            b <= 1'b1;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == true);
}

TEST_CASE("OnlyAssignedOnReset: Register always assigned outside if reset block") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    logic a, b;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            a <= '0;
            b <= 1'b1;
        end else begin
            a <= 1'b1;
        end
        b <= 1'b1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == true);
}

TEST_CASE("OnlyAssignedOnReset: Array always assigned") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    logic push, ptr;
    logic [2:0] data;
    logic [4:0][2:0] fifo;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
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

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == true);
}

TEST_CASE("OnlyAssignedOnReset: Array only assigned on reset") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    logic push, ptr;
    logic [2:0] data;
    logic [4:0][2:0] fifo;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            fifo <= '0;
        end
        else if (push) begin
            for (int i = 0; i <= 4; i++) begin
            end
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == false);
}

TEST_CASE("OnlyAssignedOnReset: Struct always assigned") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    struct {
        logic a;
        logic b;
        logic c;
    } data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
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

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == true);
}

TEST_CASE("OnlyAssignedOnReset: Struct only assigned on reset") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rst_n;
    struct {
        logic a;
        logic b;
        logic c;
    } data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            data.a <= 1'b0;
            data.b <= 1'b0;
            data.c <= 1'b0;
        end
        else begin
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    auto visitor = Registry::create("OnlyAssignedOnReset");
    bool result = visitor->check(root);
    CHECK(result == false);
}
