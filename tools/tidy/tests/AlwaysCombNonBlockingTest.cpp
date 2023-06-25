// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("AlwaysCombNonBlocking: Non blocking assignment inside always_comb") {
    auto tree = SyntaxTree::fromText(R"(
module top ();
    logic a, b;
    always_comb begin
        a <= b;
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
    auto visitor = Registry::create("AlwaysCombNonBlocking");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysCombNonBlocking: Blocking assignment inside always_comb") {
    auto tree = SyntaxTree::fromText(R"(
module top ();
    logic a, b;
    always_comb begin
        a = b;
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
    auto visitor = Registry::create("AlwaysCombNonBlocking");
    bool result = visitor->check(root);
    CHECK(result);
}
