// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("Undriven range: ") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  logic [1:0] a;
  always_comb
    a[0] = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("UndrivenRange");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

