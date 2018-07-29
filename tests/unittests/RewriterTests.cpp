#include "Test.h"

#include <fmt/format.h>

#include "lexing/SyntaxPrinter.h"
#include "parsing/SyntaxVisitor.h"

TEST_CASE("Basic rewriting") {
    class TestRewriter : public SyntaxRewriter<TestRewriter> {
    public:
        void handle(const TypedefDeclarationSyntax& decl) {
            if (decl.type->kind != SyntaxKind::EnumType)
                return;

            // Create a new localparam hardcoded with the number of entries in the enum.
            ptrdiff_t count = decl.type->as<EnumTypeSyntax>().members.size();
            auto& newNode = parse(fmt::format("localparam int {}__count = {};",
                                              decl.name.valueText(), count));
            insertAfter(decl, newNode);
        }
    };

    auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
endmodule
)");

    TestRewriter rewriter;
    tree = rewriter.transform(tree);

    std::string output = SyntaxPrinter()
        .setIncludeDirectives(true)
        .setIncludeSkipped(true)
        .setIncludeTrivia(true)
        .excludePreprocessed(tree->sourceManager())
        .print(*tree)
        .str();

    CHECK(output == R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
endmodule
)");
}