//------------------------------------------------------------------------------
//! @file EnforcePortSuffixTest.h
//! @brief Tests for the EnforcePortSuffix check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("EnforcePortSuffix: Incorrect input suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    input logic a
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct input suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    input logic a_i
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Incorrect output suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    output logic a
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct output suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    output logic a_o
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Incorrect inout suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    inout logic a
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("EnforcePortSuffix: Correct inout suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic clk_i,
    input logic rst_ni,

    inout logic a_io
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}
