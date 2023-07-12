// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("OnlyANSIPortDecl: Use of non-ANSI port declaration style") {
    auto tree = SyntaxTree::fromText(R"(
module top(a,b,c);
    input logic a;
    inout logic b;
    output logic c;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("OnlyANSIPortDecl");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("OnlyANSIPortDecl: Use of ANSI port declaration style") {
    auto tree = SyntaxTree::fromText(R"(
module top(
    input logic a,
    inout logic b,
    output logic c
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
    auto visitor = Registry::create("OnlyANSIPortDecl");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("OnlyANSIPortDecl: No port declaration") {
    auto tree = SyntaxTree::fromText(R"(
module top;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("OnlyANSIPortDecl");
    bool result = visitor->check(root);
    CHECK(result);
}
