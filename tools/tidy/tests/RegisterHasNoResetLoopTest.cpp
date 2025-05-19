// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("RegisterHasNoReset: For loop iteration variable should not trigger warning") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    logic [7:0] k;
    logic clk_i;
    logic rst_ni;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            k <= '0;
        end
        else begin
            for(int i = 0; i < 8; i += 1) begin
                k[i] <= 1'b1;
            end
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
    auto visitor = Registry::create("RegisterHasNoReset");
    bool result = visitor->check(root);
    CHECK(result);
}