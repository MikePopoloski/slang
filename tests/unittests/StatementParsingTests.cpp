#include "Test.h"

TEST_CASE("If statement", "[parser:statements]") {
    auto& text = "if (foo && bar &&& baz) ; else ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(stmt.as<ConditionalStatementSyntax>().predicate.conditions[0]->expr.kind == SyntaxKind::LogicalAndExpression);
}

TEST_CASE("Case statement (empty)", "[parser:statements]") {
    auto& text = "unique casez (foo) endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Case statement (normal)", "[parser:statements]") {
    auto& text = "unique case (foo) 3'd01: ; 3+9, foo: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Case statement (pattern)", "[parser:statements]") {
    auto& text = "priority casez (foo) matches .foo &&& bar: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Case statement (range)", "[parser:statements]") {
    auto& text = "casex (foo) inside 3, [4:2], [99]: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Loop statements", "[parser:statements]") {
    auto& text = "while (foo) ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::LoopStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Do while statement", "[parser:statements]") {
    auto& text = "do ; while (foo) ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DoWhileStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Foreach statement", "[parser:statements]") {
    auto& text = "foreach (a::b[,i,,j,]) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeachLoopStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}
TEST_CASE("Forever statement", "[parser:statements]") {
    auto& text = "forever ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeverStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Return statement", "[parser:statements]") {
    auto& text = "return foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ReturnStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Jump statements", "[parser:statements]") {
    auto& text = "break;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::JumpStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Disable statement", "[parser:statements]") {
    auto& text = "disable blah::foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Disable fork statement", "[parser:statements]") {
    auto& text = "disable fork;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableForkStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

void testTimingControl(StringRef text, SyntaxKind kind) {
    auto& stmt = parseStatement(string(text));

    REQUIRE(stmt.kind == SyntaxKind::TimingControlStatement);
    CHECK(stmt.as<TimingControlStatementSyntax>().timingControl.kind == kind);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Timing control statements", "[parser:statements]") {
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

void testStatement(StringRef text, SyntaxKind kind) {
    auto& stmt = parseStatement(string(text));

    REQUIRE(stmt.kind == kind);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Procedural assign", "[parser:statements]") {
    testStatement("assign foo = bar;", SyntaxKind::ProceduralAssignStatement);
    testStatement("force foo = bar;", SyntaxKind::ProceduralForceStatement);
    testStatement("deassign foo;", SyntaxKind::ProceduralDeassignStatement);
    testStatement("release foo;", SyntaxKind::ProceduralReleaseStatement);
}

TEST_CASE("Function calls", "[parser:statements]") {
    testStatement("foo();", SyntaxKind::ExpressionStatement);
    testStatement("void'(foo());", SyntaxKind::ExpressionStatement);
    testStatement("foo::bar.baz(blah, 324, yes);", SyntaxKind::ExpressionStatement);
}

DataDeclarationSyntax* parseBlockDeclaration(const std::string& text) {
    auto fullText = "begin " + text + " end";
    auto& stmt = parseStatement(fullText);

    REQUIRE(stmt.kind == SyntaxKind::SequentialBlockStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == fullText);

    auto& block = stmt.as<BlockStatementSyntax>();
    REQUIRE(block.items.count() == 1);
    REQUIRE(block.items[0]->kind == SyntaxKind::DataDeclaration);

    return (DataDeclarationSyntax*)block.items[0];
}

TEST_CASE("Sequential declarations", "[parser:statements]") {
    parseBlockDeclaration("logic f = 4;");
    parseBlockDeclaration("logic [3:0] f [1:4] = 4, g [99][10+:12] = new [foo] (bar);");
    parseBlockDeclaration("const var static logic f;");
    parseBlockDeclaration("foo f;");
    parseBlockDeclaration("var f;");
    parseBlockDeclaration("foo::bar#()::blah f;");
    parseBlockDeclaration("struct packed { blah blah; } f;");
    parseBlockDeclaration("enum { blah = 4 } f, h, i;");
}

TEST_CASE("Blocking Event Trigger", "[parser:statements]") {
    auto& text = "-> $root.hierarchy.evt";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::BlockingEventTriggerStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}

TEST_CASE("Nonblocking Event Trigger", "[parser:statements]") {
    auto& text = "->> # 3 hierarchy.evt";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::NonblockingEventTriggerStatement);
    CHECK(stmt.toString(SyntaxToStringFlags::IncludeTrivia) == text);
}
