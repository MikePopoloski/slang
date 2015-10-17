#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;
Preprocessor preprocessor(sourceTracker, alloc, diagnostics);

StatementSyntax* parse(const SourceText& text) {
    diagnostics.clear();
    Lexer lexer(FileID(), text, preprocessor);
    Parser parser(lexer);

    auto node = parser.parseStatement();
    REQUIRE(node);
    return node;
}

TEST_CASE("If statement", "[parser:statements]") {
    auto& text = "if (foo && bar &&& baz) ; else ;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::ConditionalStatement);
    CHECK(((ConditionalStatementSyntax*)stmt)->predicate->conditions[0]->expr->kind == SyntaxKind::LogicalAndExpression);
}

}