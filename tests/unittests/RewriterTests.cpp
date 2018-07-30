#include "Test.h"

#include <fmt/format.h>

#include "lexing/SyntaxPrinter.h"
#include "parsing/SyntaxVisitor.h"

class TestRewriter : public SyntaxRewriter<TestRewriter> {
public:
    void handle(const TypedefDeclarationSyntax& decl) {
        if (decl.type->kind != SyntaxKind::EnumType)
            return;

        // Create a new localparam hardcoded with the number of entries in the enum.
        ptrdiff_t count = decl.type->as<EnumTypeSyntax>().members.size();
        auto& newNode = parse(fmt::format("\n    localparam int {}__count = {};",
                                          decl.name.valueText(), count));
        insertAfter(decl, newNode);
    }
};

TEST_CASE("Basic rewriting") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
endmodule
)");

    tree = TestRewriter().transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
    localparam int test_t__count = 3;
endmodule
)");
}

TEST_CASE("Rewriting around macros") {
    auto tree = SyntaxTree::fromText(R"(
`define ENUM_MACRO \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } test_t

module M;
    `ENUM_MACRO
endmodule
)");

    tree = TestRewriter().transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
`define ENUM_MACRO \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } test_t

module M;
    `ENUM_MACRO
    localparam int test_t__count = 3;
endmodule
)");
}
