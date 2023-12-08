// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/syntax/AllSyntax.h"

TEST_CASE("If statement") {
    auto& text = "if (foo && bar &&& baz) ; else \n;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString() == text);
    CHECK(stmt.as<ConditionalStatementSyntax>().predicate->conditions[0]->expr->kind ==
          SyntaxKind::LogicalAndExpression);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("If statement -- missing semicolon") {
    auto& text = "begin if (foo) end";
    parseStatement(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedStatement);
}

TEST_CASE("Case statement (normal)") {
    auto& text = "unique case (foo) 3'd01: ; 3+9, foo: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Case statement (pattern)") {
    auto& text = "priority casez (foo) matches .foo &&& bar: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Case statement (range)") {
    auto& text = "casex (foo) inside 3, [4:2], [99:100]: ; default; endcase";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::CaseStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Loop statements") {
    auto& text = "while (foo) \n;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::LoopStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Do while statement") {
    auto& text = "do ; while (foo) ;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DoWhileStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Foreach statement") {
    auto& text = "foreach (a::b[,i,,j,]) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeachLoopStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Forever statement") {
    auto& text = "forever \n;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ForeverStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Return statement") {
    auto& text = "return foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ReturnStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Jump statements") {
    auto& text = "break;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::JumpStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Disable statement") {
    auto& text = "disable blah::foobar;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Disable fork statement") {
    auto& text = "disable fork;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::DisableForkStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

void testTimingControl(std::string_view text, SyntaxKind kind) {
    auto& stmt = parseStatement(std::string(text));

    REQUIRE(stmt.kind == SyntaxKind::TimingControlStatement);
    CHECK(stmt.as<TimingControlStatementSyntax>().timingControl->kind == kind);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Timing control statements") {
    testTimingControl("# 52 ;", SyntaxKind::DelayControl);
    testTimingControl("#1step ;", SyntaxKind::OneStepDelay);
    testTimingControl("# (3:4:5) ;", SyntaxKind::DelayControl);
    testTimingControl("## (3+2) ;", SyntaxKind::CycleDelay);
    testTimingControl("## foo ;", SyntaxKind::CycleDelay);
    testTimingControl("##92 ;", SyntaxKind::CycleDelay);
    testTimingControl("@* ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@ (*) ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@ (*  ) ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@ (   *  ) ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@   * ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@(posedge foo iff foo+92 == 76 or negedge clk, (edge clk)) ;",
                      SyntaxKind::EventControlWithExpression);
}

void testStatement(std::string_view text, SyntaxKind kind) {
    auto& stmt = parseStatement(std::string(text));

    REQUIRE(stmt.kind == kind);
    CHECK(stmt.toString() == text);

    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Procedural assign") {
    testStatement("assign foo = bar;", SyntaxKind::ProceduralAssignStatement);
    testStatement("force foo = bar;", SyntaxKind::ProceduralForceStatement);
    testStatement("deassign foo;", SyntaxKind::ProceduralDeassignStatement);
    testStatement("release foo;", SyntaxKind::ProceduralReleaseStatement);
}

TEST_CASE("Function calls") {
    testStatement("foo();", SyntaxKind::ExpressionStatement);
    testStatement("void'(foo());", SyntaxKind::VoidCastedCallStatement);
    testStatement("foo::bar.baz(blah, 324, yes);", SyntaxKind::ExpressionStatement);
}

TEST_CASE("Block statements") {
    testStatement("begin i = 4'b???1; j = 4'b??10; k = 4'b?100; l = 4'b1000; end",
                  SyntaxKind::SequentialBlockStatement);
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
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Blocking Event Trigger") {
    auto& text = "-> $root.hierarchy.evt;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::BlockingEventTriggerStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Nonblocking Event Trigger") {
    auto& text = "->> # 3 hierarchy.evt;";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::NonblockingEventTriggerStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Conditional expression inside conditional statement") {
    auto& text = "if (foo ? a : b) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Conditional matching statement") {
    auto& text = "if (foo matches bar &&& (baz ? 1 : 0) &&& baz) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Conditional matching expression") {
    auto& text = "if (foo matches bar &&& (baz ? 1 : 0) &&& baz ? 1 : 0) begin end";
    auto& stmt = parseStatement(text);

    REQUIRE(stmt.kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Checker statement parsing") {
    auto& text = R"(
checker c1(event clk, logic[7:0] a, b);
  logic [7:0] sum;
  always_ff @(clk) begin
    sum <= a + 1'b1;
    p0: assert property (sum < 12);
  end
  p1: assert property (@clk sum < 12);
  p2: assert property (@clk a != b);
  p3: assert #0 ($onehot(a));
endchecker

module m(input logic rst, clk, logic en, logic[7:0] in1, in2,
         in_array [20:0]);
  c1 check_outside(posedge clk, in1, in2);
  always @(posedge clk) begin
    automatic logic [7:0] v1=0;
    if (en) begin
      // v1 is automatic, so current procedural value is used
      c1 check_inside(posedge clk, in1, v1);
    end

    for (int i = 0; i < 4; i++) begin
      v1 = v1+5;
      if (i != 2) begin
        // v1 is automatic, so current procedural value is used
        c1 check_loop(posedge clk, in1, in_array[v1]);
      end
     end
  end
endmodule : m
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("randsequence parsing") {
    auto& text = R"(
module rand_sequence1();
  initial begin

	randsequence( bin_op )
		void bin_op : value operator value // void type is optional
		{ $display("%s %b %b", operator, value[1], value[2]); }
		;
		bit [7:0] value : { return $urandom; } ;
		string operator : add := 5 { return "+" ; }
						  | dec := 2 { return "-" ; }
						  | mult := 1 { return "*" ; }
						  ;
	endsequence
  end
endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("randsequence parsing error cases") {
    auto& text = R"(
module rand_sequence1();
  initial begin
    randsequence()
        foo: case(x) default: a; default: b; endcase;
        baz: rand join;
        baz: rand join a;
        bar: rand join a if (1) a else b;
    endsequence

	randsequence( bin_op )
  end
endmodule
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::MultipleDefaultCases);
    CHECK(diagnostics[1].code == diag::RandJoinNotEnough);
    CHECK(diagnostics[2].code == diag::RandJoinNotEnough);
    CHECK(diagnostics[3].code == diag::RandJoinProdItem);
    CHECK(diagnostics[4].code == diag::ExpectedRsRule);
}

TEST_CASE("Unique / priority after else parsing") {
    auto& text = R"(
module m;
    initial begin
        unique if (1) begin end
        else unique if (1) begin end
    end
endmodule
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::UniquePriorityAfterElse);
}
