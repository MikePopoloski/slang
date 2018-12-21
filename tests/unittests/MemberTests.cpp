#include "Test.h"

TEST_CASE("Nets") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    wire logic f = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Continuous Assignments") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    wire foo;
    assign foo = 1, foo = 'z;

    logic bar;
    assign bar = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}