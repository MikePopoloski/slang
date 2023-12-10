// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE(
    "NoImplicitPortNameInPortConnection: Only port name specified in module port connection") {
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
endmodule

module top ();
    logic clk, rst;
    test t (.clk, .rst(rst));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoImplicitPortNameInPortConnection");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoImplicitPortNameInPortConnection: Module port connection port by port") {
    auto tree = SyntaxTree::fromText(R"(
module test (input cl()k, input rst);
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
    auto visitor = Registry::create("NoImplicitPortNameInPortConnection");
    bool result = visitor->check(root);
    CHECK(result);
}
