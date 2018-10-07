#include "Test.h"
#include <fmt/format.h>

#include "slang/compilation/SemanticModel.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxVisitor.h"

class TestRewriter : public SyntaxRewriter<TestRewriter> {
public:
    Compilation compilation;
    SemanticModel model;

    TestRewriter(const std::shared_ptr<SyntaxTree>& tree) : model(compilation) {
        compilation.addSyntaxTree(tree);
    }

    void handle(const TypedefDeclarationSyntax& decl) {
        if (decl.type->kind != SyntaxKind::EnumType)
            return;

        // Create a new localparam hardcoded with the number of entries in the enum.
        auto type = model.getDeclaredSymbol(decl.type->as<EnumTypeSyntax>());
        REQUIRE(type);

        ptrdiff_t count = type->as<EnumType>().members().size();
        auto& newNode = parse(
            fmt::format("\n    localparam int {}__count = {};", decl.name.valueText(), count));
        insertAfter(decl, newNode);
    }
};

TEST_CASE("Basic rewriting") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
endmodule
)");

    tree = TestRewriter(tree).transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
    localparam int test_t__count = 3;
endmodule
)");
}

TEST_CASE("Rewriting around macros") {
    auto tree = SyntaxTree::fromText(R"(
`define ENUM_MACRO(asdf) \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } asdf;

module M;
    `ENUM_MACRO(test_t)
endmodule
)");

    tree = TestRewriter(tree).transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
`define ENUM_MACRO(asdf) \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } asdf;
module M;
    `ENUM_MACRO(test_t)
    localparam int test_t__count = 3;
endmodule
)");
}
