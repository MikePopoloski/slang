// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("NoDotVarInPortConnection: Use of dot var in module port connection") {
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .rst);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoDotVarInPortConnection");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoDotVarInPortConnection: Module port connection port by port") {
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk(clk), .rst(rst));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoDotVarInPortConnection");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoDotVarInPortConnection: Use of dot star in module port connection") {
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.*);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoDotVarInPortConnection");
    bool result = visitor->check(root);
    CHECK(result);
}
