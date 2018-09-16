#include "Test.h"

TEST_CASE("If statement") {
    auto& text = "if (foo && bar &&& baz) ; else ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString() == text);
    CHECK(stmt.as<ConditionalStatementSyntax>().predicate->conditions[0]->expr->kind == SyntaxKind::LogicalAndExpression);
}

TEST_CASE("Case statement (empty)") {
    auto& text = "unique casez (foo) endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Case statement (normal)") {
    auto& text = "unique case (foo) 3'd01: ; 3+9, foo: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Case statement (pattern)") {
    auto& text = "priority casez (foo) matches .foo &&& bar: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Case statement (range)") {
    auto& text = "casex (foo) inside 3, [4:2], [99]: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Loop statements") {
    auto& text = "while (foo) ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::LoopStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Do while statement") {
    auto& text = "do ; while (foo) ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DoWhileStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Foreach statement") {
    auto& text = "foreach (a::b[,i,,j,]) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeachLoopStatement);
    CHECK(stmt.toString() == text);
}
TEST_CASE("Forever statement") {
    auto& text = "forever ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeverStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Return statement") {
    auto& text = "return foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ReturnStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Jump statements") {
    auto& text = "break;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::JumpStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Disable statement") {
    auto& text = "disable blah::foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Disable fork statement") {
    auto& text = "disable fork;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableForkStatement);
    CHECK(stmt.toString() == text);
}

void testTimingControl(string_view text, SyntaxKind kind) {
    auto& stmt = parseStatement(std::string(text));

    REQUIRE(stmt.kind == SyntaxKind::TimingControlStatement);
    CHECK(stmt.as<TimingControlStatementSyntax>().timingControl->kind == kind);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Timing control statements") {
    testTimingControl("# 52 ;", SyntaxKind::DelayControl);
    testTimingControl("#1step ;", SyntaxKind::DelayControl);
    testTimingControl("# (3:4:5) ;", SyntaxKind::DelayControl);
    testTimingControl("## (3+2) ;", SyntaxKind::CycleDelay);
    testTimingControl("## foo ;", SyntaxKind::CycleDelay);
    testTimingControl("##92 ;", SyntaxKind::CycleDelay);
    testTimingControl("@* ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@ (*) ;", SyntaxKind::ParenImplicitEventControl);
    testTimingControl("@* ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@(posedge foo iff foo+92 == 76 or negedge clk, (edge clk)) ;", SyntaxKind::EventControlWithExpression);
}

void testStatement(string_view text, SyntaxKind kind) {
    auto& stmt = parseStatement(std::string(text));

    REQUIRE(stmt.kind == kind);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Procedural assign") {
    testStatement("assign foo = bar;", SyntaxKind::ProceduralAssignStatement);
    testStatement("force foo = bar;", SyntaxKind::ProceduralForceStatement);
    testStatement("deassign foo;", SyntaxKind::ProceduralDeassignStatement);
    testStatement("release foo;", SyntaxKind::ProceduralReleaseStatement);
}

TEST_CASE("Function calls") {
    testStatement("foo();", SyntaxKind::ExpressionStatement);
    testStatement("void'(foo());", SyntaxKind::ExpressionStatement);
    testStatement("foo::bar.baz(blah, 324, yes);", SyntaxKind::ExpressionStatement);
}

void parseBlockDeclaration(const std::string& text) {
    auto fullText = "begin " + text + " end";
    auto& stmt = parseStatement(fullText);

    REQUIRE(stmt.kind == SyntaxKind::SequentialBlockStatement);
    CHECK(stmt.toString() == fullText);

    auto& block = stmt.as<BlockStatementSyntax>();
    REQUIRE(block.items.size() == 1);
    REQUIRE(block.items[0]->kind == SyntaxKind::DataDeclaration);
}

TEST_CASE("Sequential declarations") {
    parseBlockDeclaration("logic f = 4;");
    parseBlockDeclaration("logic [3:0] f [1:4] = 4, g [99][10+:12] = new [foo] (bar);");
    parseBlockDeclaration("const var static logic f;");
    parseBlockDeclaration("foo f;");
    parseBlockDeclaration("var f;");
    parseBlockDeclaration("foo::bar#()::blah f;");
    parseBlockDeclaration("struct packed { blah blah; } f;");
    parseBlockDeclaration("enum { blah = 4 } f, h, i;");
}

TEST_CASE("Blocking Event Trigger") {
    auto& text = "-> $root.hierarchy.evt";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::BlockingEventTriggerStatement);
    CHECK(stmt.toString() == text);
}

TEST_CASE("Nonblocking Event Trigger") {
    auto& text = "->> # 3 hierarchy.evt";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::NonblockingEventTriggerStatement);
    CHECK(stmt.toString() == text);
}
