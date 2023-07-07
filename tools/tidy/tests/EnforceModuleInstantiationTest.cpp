// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("EnforceModuleInstantiationPrefix: Incorrect module instantiation prefix") {
    auto tree = SyntaxTree::fromText(R"(
module test ();
endmodule

module top();
    test test();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforceModuleInstantiationPrefix");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("EnforceModuleInstantiationPrefix: Correct module instantiation prefix") {
    auto tree = SyntaxTree::fromText(R"(
module test ();
endmodule

module top();
    test i_test();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("EnforceModuleInstantiationPrefix");
    bool result = visitor->check(root);
    CHECK(result);
}
