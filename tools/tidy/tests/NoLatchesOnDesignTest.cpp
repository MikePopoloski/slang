// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("NoLatchesOnDesign: Design with latch") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic a,
    output logic b
);
    always_latch begin
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
    auto visitor = Registry::create("NoLatchesOnDesign");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoLatchesOnDesign: Design without latch") {
    auto tree = SyntaxTree::fromText(R"(
module top (
    input logic a,
    output logic b
);
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
    auto visitor = Registry::create("NoLatchesOnDesign");
    bool result = visitor->check(root);
    CHECK(result);
}
