// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

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
    Registry::setSourceManager(compilation.getSourceManager());
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
    Registry::setSourceManager(compilation.getSourceManager());
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
    Registry::setSourceManager(compilation.getSourceManager());
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
    Registry::setSourceManager(compilation.getSourceManager());
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
    Registry::setSourceManager(compilation.getSourceManager());
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
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Multiple suffixes for input port") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic in_a,
    input logic in_b,
    input logic in_c
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    config.getCheckConfigs().inputPortSuffix = {"_a", "_b", "_c"};
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Ignore some port suffixes") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic abc,
    output logic bcd
);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    config.getCheckConfigs().inputPortSuffix = {};
    config.getCheckConfigs().outputPortSuffix = {""};
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Explicit ports") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input .data_i({a1, b1}),
    output .data_o({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("EnforcePortSuffix: Explicit port with incorrect suffix") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input .data_i({a1, b1}),
    input .data_o({a2, b2})
);
    logic a1, a1, a2, b2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforcePortSuffix");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}
