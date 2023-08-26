// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("CastSignedIndex: Negative index") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a [4];

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            a[2'(i)] = i;
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
    auto visitor = Registry::create("CastSignedIndex");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("CastSignedIndex: Signed index") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a [4];

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            a[i] = i;
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
    auto visitor = Registry::create("CastSignedIndex");
    bool result = visitor->check(root);
    CHECK(result);
}
