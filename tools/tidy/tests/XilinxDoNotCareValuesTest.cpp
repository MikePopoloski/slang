// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("XilinxDoNotCareValues: Use of 'd") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic [3:0] a = 4'd?;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("XilinxDoNotCareValues");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("XilinxDoNotCareValues: Use of 'b") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic [3:0] a = 4'b?;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("XilinxDoNotCareValues");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("XilinxDoNotCareValues: No do-not-care values") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic [3:0] a = 4'd10;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("XilinxDoNotCareValues");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("XilinxDoNotCareValues: No do-not-care values but with comment") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic [3:0] a =
       /*'d?*/4'd10;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("XilinxDoNotCareValues");
    bool result = visitor->check(root);
    CHECK(result);
}
