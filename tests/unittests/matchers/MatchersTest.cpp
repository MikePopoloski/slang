// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <iostream>

#include "slang/matchers/MatchFinder.h"
#include "slang/matchers/Matchers.h"

using namespace slang::ast::matchers;

class Callback : public MatcherCallback {
public:
    bool found = false;
    void run(const MatchResult&) override { found = true; }
};

TEST_CASE("Match basic") {
    const auto tree = SyntaxTree::fromText(R"(
module top();
    logic a;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();

    const auto context = ASTContext(compilation.createScriptScope(), LookupLocation::max);
    MatchFinder finder(context);
    Callback callback;
    finder.addMatcher(varDecl().bind("var_a"), &callback);
    finder.match(root);

    CHECK(callback.found);
}
