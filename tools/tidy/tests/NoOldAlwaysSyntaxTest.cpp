//------------------------------------------------------------------------------
//! @file NoOldAlwaysSyntaxTest.h
//! @brief Test for the NoOldAlwaysSyntax check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("NoOldAlwaysSyntax: Use of old always_comb syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;

    always @(*) begin
        c = a + b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoOldAlwaysSyntax: Use of old always_ff syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;

    always @(posedge a) begin
        c <= a + b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoOldAlwaysSyntax: Use of SV always_ff and always_comb syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;
    logic d, e, f;

    always_ff @(posedge a) begin
        c <= a + b;
    end

    always_comb begin
        d = e + f;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}
