// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("AlwaysFFAssignmentOutsideConditional: Assignment inside always_ff and outside if "
          "statement with reset") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk_i;
    logic rst_ni;
    logic foo, bar;
    int a;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        foo <= bar;
        if(rst_ni) a <= '0;
        else    a <= a +1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("AlwaysFFAssignmentOutsideConditional");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysFFAssignmentOutsideConditional: All assignments inside either if or else "
          "statements inside the always_ff block") {
    auto tree = SyntaxTree::fromText(R"(
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

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("AlwaysFFAssignmentOutsideConditional");
    bool result = visitor->check(root);
    CHECK(result);
}
