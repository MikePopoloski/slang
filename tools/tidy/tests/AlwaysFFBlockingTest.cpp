// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("AlwaysFFBlocking: Blocking assignment inside always_ff") {
    auto tree = SyntaxTree::fromText(R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
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
    auto visitor = Registry::create("AlwaysFFBlocking");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysFFBlocking: Correct blocking assignment inside always_ff") {
    auto tree = SyntaxTree::fromText(R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
        int k = 1;
        k = 42;
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
    auto visitor = Registry::create("AlwaysFFBlocking");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("AlwaysFFBlocking: Incorrect blocking assignment inside always_ff") {
    auto tree = SyntaxTree::fromText(R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
        int k = 1;
        k = 42;
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
    auto visitor = Registry::create("AlwaysFFBlocking");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}
