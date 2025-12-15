// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/format.h>

#include "slang/diagnostics/StatementsDiags.h"

TEST_CASE("Named sequences") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence seq(x, y, min, max, delay1);
        x ##delay1 y[*min:max];
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Named properties") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic a,b,c,d,e,f;

    property p1(x,y);
        ##1 x |-> y;
    endproperty

    wire clk;
    property p2;
        @(posedge clk)
        a ##1 (b || c)[->1] |->
            if (b)
                p1(d,e)
            else
                f;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Concurrent assertion expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string a;
    logic b,c,d,e;

    foo: assert property (a);
    assert property (a ##1 b ##[+] c ##[*] d ##[1:5] e);
    assert property (##0 a[*1:4] ##0 b[=4] ##0 c[->1:2] ##0 c[*] ##1 d[+]);
    assert property (##[1:$] a[*0:$]);
    assert property ((a ##0 b) and (c or d));
    assert property ((a ##0 b) and (c or d));
    assert property (a intersect b and d throughout e within c);
    assert property (a iff b until d s_until e until_with c s_until_with d);
    assert property (((a)) |-> b |=> (d implies (e #-# (d #=# a))));
    assert property ((a within b) within (((c))[*3]));
    assert property (((a)) throughout c);
    assert property ((@(posedge b) a and b) intersect c);
    assert property ((@(posedge b) a iff b) implies c);
    assert property (first_match(a and b));
    assert property (always b and c);
    assert property ((s_always [3:4] b and c) and (s_eventually [1:$] b) and (eventually [1:2] c));
    assert property ((nexttime [3] b) and (s_nexttime b));
    assert property (strong(a ##1 b) and weak(a intersect b));
    assert property (not a ##1 b);
    assert property (accept_on(b) sync_reject_on(c) sync_accept_on(d) reject_on(e) b ##1 c);
    assume property (if (b) a ##1 c else d ##1 e);
    cover property (case (b) 1, 2, 3: 1 ##1 b; 4: a and b; default: 1 or b; endcase);
    restrict property (@(posedge b) ((b) and b) ##0 b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Concurrent assertion expression errors") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int bar;
endclass

function int func(output o);
endfunction

module m;
    int a[];
    logic b;
    chandle c;
    C d = new;
    logic o;
    localparam real p = 3.14;

    assert property (a ##1 b++);
    assert property (c == null);
    assert property (d.bar);
    assert property (func(o));
    assert property (b[* -1:4]);
    assert property (b ##[4:1] b);
    assert property (b ##p b);
    assert property (##0 b[*3-:4] ##0 b[=]);
    assert property (##[] b ##[1+:5] b);
    assert property ((b iff b) |-> b);
    assert property ((b and b)[*3] throughout b);
    assert property (b[*3] throughout b);
    assert property (always [] b);
    assert property (always [4] b);
    assert property (s_always b);
    assert property (nexttime [1:2] b);
    assert property (eventually [1:$] b);
    assert property (b or @o);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 21);
    CHECK(diags[0].code == diag::AssertionExprType);
    CHECK(diags[1].code == diag::IncDecNotAllowed);
    CHECK(diags[2].code == diag::CHandleInAssertion);
    CHECK(diags[3].code == diag::ClassMemberInAssertion);
    CHECK(diags[4].code == diag::AssertionFuncArg);
    CHECK(diags[5].code == diag::ValueMustBePositive);
    CHECK(diags[6].code == diag::SeqRangeMinMax);
    CHECK(diags[7].code == diag::ExprMustBeIntegral);
    CHECK(diags[8].code == diag::InvalidRepeatRange);
    CHECK(diags[9].code == diag::ExpectedExpression);
    CHECK(diags[10].code == diag::ExpectedExpression);
    CHECK(diags[11].code == diag::InvalidRepeatRange);
    CHECK(diags[12].code == diag::PropertyLhsInvalid);
    CHECK(diags[13].code == diag::ThroughoutLhsInvalid);
    CHECK(diags[14].code == diag::ThroughoutLhsInvalid);
    CHECK(diags[15].code == diag::ExpectedExpression);
    CHECK(diags[16].code == diag::InvalidPropertyRange);
    CHECK(diags[17].code == diag::InvalidPropertyRange);
    CHECK(diags[18].code == diag::InvalidPropertyIndex);
    CHECK(diags[19].code == diag::UnboundedNotAllowed);
    CHECK(diags[20].code == diag::ExpectedExpression);
}

TEST_CASE("Sequence & property instances") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    assert property (n.a(3));
    assert property (b);

    logic c, d;
    sequence b;
        ##1 c ##1 d;
    endsequence
endmodule

module n;
    logic c, d;
    property a(int i, foo = 1);
        ##1 c ##1 d ##1 i > 0;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assertion instance arg errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    assert property (a(, .a(1), .b(), .d(1)));
    assert property (a(1, 2));
    assert property (a(1, 2, 3, 4));

    sequence a(a, b, c);
        1;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::UnconnectedArg);
    CHECK(diags[1].code == diag::ArgCannotBeEmpty);
    CHECK(diags[2].code == diag::DuplicateArgAssignment);
    CHECK(diags[3].code == diag::ArgCannotBeEmpty);
    CHECK(diags[4].code == diag::ArgDoesNotExist);
    CHECK(diags[5].code == diag::TooFewArguments);
    CHECK(diags[6].code == diag::TooManyArguments);
}

TEST_CASE("Assertion instance arg type checking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[];
    assert property (a(1, 1 iff 1, foo, 1 and 1));
    assert property (a(1 iff 1, 1, 1));
    assert property (a(1, 1, foo[*]));

    int e;
    property a(sequence a, property b, int c[], untyped d = e);
        1;
    endproperty

    sequence b(int i, untyped j);
        1 ##[i:j] 1;
    endsequence

    assert property (b($, $));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::AssertionArgTypeSequence);
    CHECK(diags[1].code == diag::AssertionArgTypeMismatch);
    CHECK(diags[2].code == diag::AssertionArgNeedsRegExpr);
    CHECK(diags[3].code == diag::UnboundedNotAllowed);
}

TEST_CASE("Assertion instance arg expansion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [7:0] bar;

    assert property (s1($, 5));
    assert property (s1(bar, 9.2));
    assert property (s3(1));
    assert property (s4(1 and 1));

    sequence s1(a, int b);
        s2(a) ##1 bar[b:0] > 0;
    endsequence

    sequence s2(foo);
        1 ##[0:foo] 1 ##1 foo > 0;
    endsequence

    sequence s3(sequence a);
        1 ##[0:a] 1;
    endsequence

    sequence s4(foo);
        foo ##1 1 + foo;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UnboundedNotAllowed);
    CHECK(diags[1].code == diag::RangeOOB);
    CHECK(diags[2].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[3].code == diag::AssertionDelayFormalType);
    CHECK(diags[4].code == diag::BadBinaryExpression);
}

TEST_CASE("More complex sequence arg expansion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s1;
        logic foo;
        s2(s2(foo));
    endsequence

    sequence s2(a);
        a;
    endsequence

    assert property (s1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Default disable declarations") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    default disable iff i > 1;
endmodule

module n;
    int a, b;
    default disable iff a > 0;
    default disable iff b > 0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleDefaultDisable);
}

TEST_CASE("Hierarchical access to assertion ports") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s(int i);
        i;
    endsequence

    int i = s.i;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::TooFewArguments);
}

TEST_CASE("Local vars in assertions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s(int i);
        int j, k = j;
        (i > 0 && j > 0, j = 1, j++)[*0:1];
    endsequence

    int baz;
    sequence s2;
        int j, k = j;
        first_match(j > 0, !j, j + k, baz = 1, baz++);
    endsequence

    typedef int Foo;
    property p;
        Foo u, v;
        s(u) and v > 0 and s2;
    endproperty

    assert property (p);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InvalidMatchItem);
    CHECK(diags[1].code == diag::InvalidMatchItem);
    CHECK(diags[2].code == diag::LocalVarMatchItem);
    CHECK(diags[3].code == diag::LocalVarMatchItem);
}

TEST_CASE("Local vars default values") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s(i);
        int j, k = j, l = i, m = baz;
        (i > 0 && j > 0, j = 1, j++)[*1:2];
    endsequence
    assert property (s(3));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Sequence triggered method") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk, ready;
    sequence e1;
        @(posedge clk) $rose(ready) ##1 1 ##1 1;
    endsequence

    sequence rule;
        @(posedge clk) e1.triggered ##1 1;
    endsequence

    sequence e2(a,b,c);
        @(posedge clk) $rose(a) ##1 b ##1 c;
    endsequence

    wire proc1, proc2;
    sequence rule2;
        @(posedge clk) e2(ready,proc1,proc2).triggered ##1 1;
    endsequence

    sequence e3(sequence a, untyped b);
        @(posedge clk) a.triggered ##1 b;
    endsequence

    sequence rule3;
        @(posedge clk) e3(ready ##1 proc1, proc2) ##1 1;
    endsequence

    assert property (rule);
    assert property (rule2);
    assert property (rule3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Sequence matched method") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk;
    sequence e1(a,b,c);
        @(posedge clk) $rose(a) ##1 b ##1 c ;
    endsequence

    wire reset, inst, ready, proc1, proc2, branch_back;
    sequence e2;
        @(posedge clk) reset ##1 inst ##1 e1(ready,proc1,proc2).matched [->1]
        ##1 branch_back;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Sequence triggered local vars") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s1(sequence a);
        ##1 a.triggered;
    endsequence

    sequence s2(a);
        s1(a);
    endsequence

    sequence s3(local int foo); 1; endsequence
    sequence s4;
        s2(s3(1));
    endsequence

    sequence s5(a, event b, sequence c);
        a > 0 ##1 c ##1 @b 1;
    endsequence

    event e;
    sequence s6;
        int i;
        logic j;
        s5(i + 1, e, i + 1 > 0).triggered ##1 s5(i, e, j).triggered;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::SeqMethodInputLocalVar);
    CHECK(diags[1].code == diag::SequenceMethodLocalVar);
    CHECK(diags[2].code == diag::SequenceMethodLocalVar);
}

TEST_CASE("Sequence event control") {
    auto tree = SyntaxTree::fromText(R"(
wire a, b, c, clk;
sequence abc;
    @(posedge clk) a ##1 b ##1 c;
endsequence

module m;
    initial begin
        @ abc $display("Saw a-b-c");
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Level-sensitive sequence control") {
    auto tree = SyntaxTree::fromText(R"(
wire a, b, c, clk;
sequence abc;
    @(posedge clk) a ##1 b ##1 c;
endsequence

wire d, e;
sequence de;
    @(negedge clk) d ##[2:5] e;
endsequence

program check;
    initial begin
        wait (abc.triggered || de.triggered);
        if (abc.triggered)
            $display("abc succeeded");
        if (de.triggered)
            $display("de succeeded");
    end
endprogram
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive sequence expansion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s1;
        s2;
    endsequence

    sequence s2;
        s1;
    endsequence

    assert property (s1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::RecursiveSequence);
    CHECK(diags[1].code == diag::RecursiveSequence);
}

TEST_CASE("Recursive property") {
    auto tree = SyntaxTree::fromText(R"(
logic write_request, write_request_ack;
logic [0:127] data, model_data;
logic [3:0] write_request_ack_tag, data_valid_tag, retry_tag;
logic data_valid;
logic retry;
logic last_data_valid;
logic reset;

property check_write;
    logic [0:127] expected_data;
    logic [3:0] tag;
    disable iff (reset) (
        write_request && write_request_ack,
        expected_data = model_data,
        tag = write_request_ack_tag
    )
    |=> check_write_data_beat(expected_data, tag, 4'h0);
endproperty

property check_write_data_beat(
    local input logic [0:127] expected_data,
    local input logic [3:0]   tag, i
);
    (
        (data_valid && (data_valid_tag == tag)) ||
        (retry && (retry_tag == tag))
    )[->1]
    |-> ((
            (data_valid && (data_valid_tag == tag))
            |-> (data[0:7] == expected_data[i*8+:8])
        )
        and (
            if (retry && (retry_tag == tag)) (
                1'b1 |=> check_write_data_beat(expected_data, tag, 4'h0)
            ) else if (!last_data_valid) (
                1'b1 |=> check_write_data_beat(expected_data, tag, i+4'h1)
            ) else (
                ##1 (retry && (retry_tag == tag))
                |=> check_write_data_beat(expected_data, tag, 4'h0)
            )
        )
    );
endproperty

property prop(p, bit b, abort);
  (p and (1'b1 |=> recProp(p, b, abort)));
endproperty

property recProp(p, bit b, abort);
  accept_on(b) reject_on(abort) prop(p, b, abort);
endproperty

module m;
    assert property (check_write);

    logic p;
    bit b;
    logic abort;
    assert property(prop(p, b, abort));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Event argument to sequence instance") {
    auto tree = SyntaxTree::fromText(R"(
logic x,y;
sequence event_arg_example (event ev);
    @(ev) x ##1 y;
endsequence

sequence s2 (ev);
    @(ev) x ##1 y;
endsequence

module m;
    logic clk;

    cover property (event_arg_example(clk));
    cover property (event_arg_example(posedge clk));
    cover property (event_arg_example((posedge clk iff x or edge clk, x iff y, negedge clk)));
    cover property (event_arg_example((x iff y, negedge clk)));
    cover property (event_arg_example(((x iff y) or negedge clk)));

    cover property (s2(clk));
    cover property (s2(posedge clk));
    cover property (s2((posedge clk iff x or edge clk, x iff y, negedge clk)));
    cover property (s2((x iff y, negedge clk)));
    cover property (s2(((x iff y) or negedge clk)));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Sequence event expr errors") {
    auto tree = SyntaxTree::fromText(R"(
logic x,y;
sequence s1 (event ev);
    @(ev) x ##1 y;
endsequence

module m;
    logic clk;
    sequence s2;
        ##1 (1, posedge clk) ##1 posedge clk;
    endsequence

    sequence s3(event ev);
        ##1 ev;
    endsequence

    property s4;
        (x iff y, 1);
    endproperty

    assert property (s1((x and y) iff clk));
    assert property (s1((x and y)[*0:1]));
    assert property (s1(x[*0:1]));
    assert property (s1(x |-> y));
    assert property (s1(x throughout y));
    assert property (s3(x));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::InvalidMatchItem);
    CHECK(diags[1].code == diag::InvalidSignalEventInSeq);
    CHECK(diags[2].code == diag::EventExprAssertionArg);
    CHECK(diags[3].code == diag::InvalidCommaInPropExpr);
    CHECK(diags[4].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[5].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[6].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[7].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[8].code == diag::InvalidSyntaxInEventExpr);
}

TEST_CASE("Restrict / expect / cover statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic clk, i;
    initial begin
        cover property (@(posedge clk) i);
        cover sequence (@(posedge clk) i);
        restrict property (@(posedge clk) i);
        expect (@(posedge clk) i);

        restrict property (@(posedge clk) i) i++;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RestrictStmtNoFail);
}

TEST_CASE("Property in event expression error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    property p; 1; endproperty
    initial begin
        @(p);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidEventExpression);
}

TEST_CASE("Invalid assertion port array types") {
    auto tree = SyntaxTree::fromText(R"(
property p(a, b[3], untyped c[2], sequence d, e[4]); 1; endproperty
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidArrayElemType);
    CHECK(diags[1].code == diag::InvalidArrayElemType);
    CHECK(diags[2].code == diag::InvalidArrayElemType);
}

TEST_CASE("Sequence with property port") {
    auto tree = SyntaxTree::fromText(R"(
sequence s(property p);
    1;
endsequence
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::PropertyPortInSeq);
}

TEST_CASE("Prop expressions inside sequences") {
    auto tree = SyntaxTree::fromText(R"(
property p; 1; endproperty

sequence s(a, sequence b, untyped c);
    p() or a or c;
endsequence

module m;
    wire clk, a;
    assert property (s(@(posedge clk) a |-> clk, p, p within clk));
    assert property (p and p);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::PropExprInSequence);
    CHECK(diags[1].code == diag::PropExprInSequence);
    CHECK(diags[2].code == diag::PropExprInSequence);
    CHECK(diags[3].code == diag::PropExprInSequence);
}

TEST_CASE("Invalid assertion instance repetitions") {
    auto tree = SyntaxTree::fromText(R"(
property p; 1; endproperty
sequence s; 1; endsequence

module m;
    assert property (p [*3]);
    assert property (s [=3]);
    assert property ((1 ##1 1) [-> 3]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::PropInstanceRepetition);
    CHECK(diags[1].code == diag::SeqInstanceRepetition);
    CHECK(diags[2].code == diag::SeqInstanceRepetition);
}

TEST_CASE("Formal arg types for sequence delay / abbrev") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s(shortint x, logic [31:0] y, byte z);
        1 ##x 1 ##y 1 ##z 1;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::AssertionDelayFormalType);
    CHECK(diags[1].code == diag::AssertionDelayFormalType);
}

TEST_CASE("Local var formal arg") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic a;
    int b,c;
    int data_in, data_out;

    sequence sub_seq2(local inout int lv);
        (a ##1 !a, lv += data_in)
        ##1 !b[*0:$] ##1 b > 0 && (data_out == lv);
    endsequence

    sequence seq2;
        int v1;
        (c > 0, v1 = data_in)
        ##1 sub_seq2(v1)
        ##1 (data_out == v1);
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Local var formal arg errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic b_d, d_d;
    sequence legal_loc_var_formal (
        local inout logic a,
        local logic b = b_d,
                    c,
                    d = d_d,
        logic e, f
    );
        logic g = c, h = g || d;
        (1, e = 1);
    endsequence

    sequence illegal_loc_var_formal (
        output logic a,
        local inout logic b,
                          c = 1'b0,
        local             d = 1 + 2,
        local event e,
        local logic f = g
    );
        logic g = b;
        1[*0];
    endsequence

    assert property (legal_loc_var_formal(1, 1, 1, 1, 1, 1));

    property p(local inout logic a, local output logic b);
        1;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::AssertionPortTypedLValue);
    CHECK(diags[1].code == diag::AssertionPortDirNoLocal);
    CHECK(diags[2].code == diag::AssertionPortOutputDefault);
    CHECK(diags[3].code == diag::LocalVarTypeRequired);
    CHECK(diags[4].code == diag::AssertionExprType);
    CHECK(diags[5].code == diag::UndeclaredIdentifier);
    CHECK(diags[6].code == diag::LocalVarOutputEmptyMatch);
    CHECK(diags[7].code == diag::AssertionOutputLocalVar);
    CHECK(diags[8].code == diag::AssertionPortPropOutput);
    CHECK(diags[9].code == diag::AssertionPortPropOutput);
}

TEST_CASE("Match items + empty match") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic a,b,c;
    sequence s;
        int x,e;
        a ##1 (b[*0:1], x = e) ##1 c[*];
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MatchItemsAdmitEmpty);
}

TEST_CASE("Subroutine match items") {
    auto tree = SyntaxTree::fromText(R"(
function automatic void foo(logic v, ref logic w);
endfunction

function int bar(output v);
endfunction

module m;
    logic a,e,b,f;
    sequence s1;
        logic v, w;
        (a, v = e) ##1
        (b[->1], w = f, $display("%h,%h\n", v, w)) ##1
        (a, foo(v, w)) ##1
        (a, bar(v));
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::SubroutineMatchAutoRefArg);
    CHECK(diags[1].code == diag::SubroutineMatchNonVoid);
    CHECK(diags[2].code == diag::SubroutineMatchOutArg);
}

TEST_CASE("Illegal disable iff instantiations") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk;
    property p;
        @(posedge clk) disable iff (clk) 1;
    endproperty

    property q;
        disable iff (clk) p();
    endproperty

    property r;
        1 |-> p();
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NestedDisableIff);
    CHECK(diags[1].code == diag::NestedDisableIff);
}

TEST_CASE("disable iff condition restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s;
        1;
    endsequence

    wire clk;
    property p;
        bit a;
        @(posedge clk) disable iff (a || s.matched) 1;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::DisableIffLocalVar);
    CHECK(diags[1].code == diag::DisableIffMatched);
}

TEST_CASE("abort property condition restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s;
        1;
    endsequence

    wire clk;
    property p;
        bit a;
        @(posedge clk) accept_on (a || s.matched) 1;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::PropAbortLocalVar);
    CHECK(diags[1].code == diag::PropAbortMatched);
}

TEST_CASE("Sequence properties with empty matches") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s;
        1[*0];
    endsequence

    property p;
        strong(s) and s;
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::SeqEmptyMatch);
    CHECK(diags[1].code == diag::SeqEmptyMatch);
}

TEST_CASE("Illegal property recursion cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    property prop_always(p);
        p and (1'b1 |=> prop_always(p));
    endproperty

    property illegal_recursion_1(p);
        not prop_always(not p);
    endproperty

    property illegal_recursion_2(p);
        p and (1'b1 |=> not illegal_recursion_2(p));
    endproperty

    logic b;
    property illegal_recursion_3(p);
        disable iff (b)
        p and (1'b1 |=> illegal_recursion_3(p));
    endproperty

    property illegal_recursion_4(p);
        p and (1'b1 |-> illegal_recursion_4(p));
    endproperty

    property fibonacci1 (local input int a, b, n, int fib_sig);
        (n > 0)
        |->
        (
            (fib_sig == a)
            and
            (1'b1 |=> fibonacci1(b, a + b, n - 1, fib_sig))
        );
    endproperty

    property fibonacci2 (int a, b, n, fib_sig);
        (n > 0)
        |->
        (
            (fib_sig == a)
            and
            (1'b1 |=> fibonacci2(b, a + b, n - 1, fib_sig))
        );
    endproperty
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::RecursivePropNegation);
    CHECK(diags[1].code == diag::RecursivePropNegation);
    CHECK(diags[2].code == diag::RecursivePropDisableIff);
    CHECK(diags[3].code == diag::RecursivePropTimeAdvance);
    CHECK(diags[4].code == diag::RecursivePropArgExpr);
    CHECK(diags[5].code == diag::RecursivePropArgExpr);
    CHECK(diags[6].code == diag::RecursivePropArgExpr);
}

TEST_CASE("Illegal concurrent assertions in action blocks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    assert property (1) begin assume property (1); end else cover property (1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConcurrentAssertActionBlock);
    CHECK(diags[1].code == diag::ConcurrentAssertActionBlock);
}

TEST_CASE("Sequence with dist expression") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk, req;
    assume property (@(posedge clk) req dist {0:=40, 1:=60});
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Property port crash regression GH #451") {
    auto tree = SyntaxTree::fromText(R"(
property prop(a);
    logic [$bits(a)-1:0] b;
    1;
endproperty
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Seq expr parsing regress GH #473") {
    auto tree = SyntaxTree::fromText(R"(
module top(
    input logic clk
);
    localparam I_MAX = 4;
    localparam J_MAX = 2;
    logic a, b, c;
    logic [J_MAX-1:0][I_MAX-1:0] sig_a, sig_b, sig_c;

    COVER_PASS: cover property ( @(posedge clk)
        a ##[0:$]
        b ##1
        c [*0:$] ##0
        ~c
    ) $info("%t %m HIT", $time);

    COVER_FAIL: cover property ( @(posedge clk)
        sig_a[0][0] ##[0:$]
        sig_b[0][0] ##1
        sig_c[0][0] [*0:$] ##0
        ~sig_c[0][0]
    ) $info("%t %m HIT", $time);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("$past in $bits regress GH #509") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk, reset, a, b, c;
    assert property(@(posedge clk) disable iff (reset)
        a |-> {500-$bits($past(b)){1'b1}} != 0);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assertion local var in event expression") {
    auto tree = SyntaxTree::fromText(R"(
sequence s;
    int x;
    @(x) 1 ##1 1;
endsequence
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::LocalVarEventExpr);
}

TEST_CASE("Inferred value system functions") {
    auto tree = SyntaxTree::fromText(R"(
module m(logic a, b, c, d, rst1, clk1, clk2);
    logic rst;

    default clocking @(negedge clk1); endclocking
    default disable iff rst1;

    property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                        rst = $inferred_disable);
        @clk disable iff (rst)
            (start_event ##0 end_event[->1]) |=> form;
    endproperty

    property p_triggers2(start_event, end_event, form, event clk = $inferred_clock,
                         bit rst = $inferred_disable);
        @clk disable iff (rst)
            (start_event ##0 end_event[->1]) |=> form;
    endproperty

    property p_multiclock(clkw, clkx = $inferred_clock, clky, w, x, y, z);
        @clkw w ##1 @clkx x |=> @clky y ##1 z;
    endproperty

    a1: assert property (p_triggers(a, b, c));
    a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

    always @(posedge clk2 or posedge rst) begin
        if (rst) begin end
        else begin
            a3: assert property (p_triggers(a, b, c));
        end
    end

    a4: assert property(p_multiclock(negedge clk2, , posedge clk1,
                                     a, b, c, d) );
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Inferred value system function errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    event e = $inferred_clock;
    property p_triggers(bit clk = $inferred_clock, rst = $inferred_disable);
        @clk disable iff (rst) 1;
    endproperty

    property p_triggers2(rst = $inferred_disable() || 0);
        1;
    endproperty

    a1: assert property (p_triggers());
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InferredValDefArg);
    CHECK(diags[1].code == diag::AssertionArgTypeMismatch);
    CHECK(diags[2].code == diag::InferredValDefArg);
}

TEST_CASE("Duplicate assertion local variable error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s;
        int foo;
        int foo;
        1;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::Redefinition);
}

TEST_CASE("Assertion clocking events can't reference auto vars") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        automatic logic p;
        assert property (@(posedge p) 1);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AutoFromNonProcedural);
}

TEST_CASE("Assertion repetition error checking regress -- GH #1004") {
    auto tree = SyntaxTree::fromText(R"(
module test(
    input logic A,
    input logic B,
    input logic clk
);
    assert property (@(posedge clk) A |=> ##[C] B);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Sequence nondegeneracy tests 1") {
    auto test = [](std::string_view expr, std::optional<DiagCode> code = {}) {
        auto tree = SyntaxTree::fromText(fmt::format(R"(
module top;
    string a;
    logic b;
    logic c, d, e;
    assert property ({});
endmodule
)",
                                                     expr));
        Compilation compilation;
        compilation.addSyntaxTree(tree);

        auto& diags = compilation.getAllDiagnostics();
        if (!code) {
            CHECK(diags.empty());
            if (!diags.empty())
                FAIL_CHECK(expr);
        }
        else if (diags.size() != 1 || diags[0].code != code) {
            FAIL_CHECK(expr);
            CHECK(diags.size() == 1);
            if (diags.size() == 1)
                CHECK(diags[0].code == *code);
        }
    };

    test("(1'b1 ##[1:2] 1'b1) intersect (1'b1 ##[2:4] 1'b1)");
    test("(1'b1 ##[1:2] 1'b1) intersect (1'b1 ##[3:4] 1'b1)", diag::SeqNoMatch);
    test("(1'b1) intersect (1'b1[*0] ##2 1'b1)", diag::SeqNoMatch);
    test("(1'b1 ##1 1'b1) intersect (1'b1[*0] ##2 1'b1)");
    test("(1'b1 ##1 1'b0) intersect (1'b1[*0] ##2 1'b1)", diag::SeqNoMatch);
    test("(1'b1) intersect (1'b1 ##[1:3] 1'b1)", diag::SeqNoMatch);
    test("(1'b1 ##1 1'b1) intersect (1'b1 ##[1:3] 1'b1)");
    test("(1'b1 ##0 1'b1) intersect (1'b1 ##[1:3] 1'b1)", diag::SeqNoMatch);
    test("(1'b1[*2]) intersect (1'b1 ##[1:3] 1'b1)");
    test("(##2 1'b1[*2]) intersect (1'b1 ##[1:3] 1'b1)");
    test("##0 a[*0:4] ##0 b[=4] ##0 c[->1:2] ##0 c[*] ##1 d[+]");
    test("##0 a[*0:4] ##0 b[=4] ##0 c[->1:2] ##0 c[*0] ##1 d[+]", diag::SeqNoMatch);
    test("##0 a[*0] ##0 b[=4] ##0 c[->1:2] ##0 c[*] ##1 d[+]", diag::SeqNoMatch);

    test("((1 ##5 1) or (1 ##8 1)) intersect (1 ##7 1)");
    test("(a[->1:$] intersect b[*5]) within 1", diag::SeqNoMatch);
    test("(a[->1:4] intersect b[->5:$]) within 1", diag::SeqNoMatch);
    test("(a[->1:4] intersect b[->5:7]) within 1", diag::SeqNoMatch);
}

TEST_CASE("Sequence nondegeneracy tests 2") {
    auto test = [](std::string_view expr, std::optional<DiagCode> code = {}) {
        auto tree = SyntaxTree::fromText(fmt::format(R"(
module top(a, b, e);
    input a;
    input b;
    input e;
    logic c, d;
    logic clk;

    property p;
        {};
    endproperty

    assert property (p);
endmodule
)",
                                                     expr));
        Compilation compilation;
        compilation.addSyntaxTree(tree);

        auto& diags = compilation.getAllDiagnostics();
        if (!code) {
            CHECK(diags.empty());
            if (!diags.empty())
                FAIL_CHECK(expr);
        }
        else if (diags.size() != 1 || diags[0].code != code) {
            FAIL_CHECK(expr);
            CHECK(diags.size() == 1);
            if (diags.size() == 1)
                CHECK(diags[0].code == *code);
        }
    };

    test("!(2'b01 - 2'b01 + 3'b010 - 3'b010 + 4'b0010)", diag::SeqNoMatch);
    test("(2'b01 - 2'b01 + 3'b010 - 3'b010 + 4'b0010) > 0");
    test("a[*0] |-> b", diag::SeqOnlyEmpty);
    test("a[*1] |-> b");
    test("1'b1 ##1 b");

    test("##0 c");
    test("1'b1 ##1 1'b0 ##0 d ##1 1'b1", diag::SeqNoMatch);
    test("1'b1 ##1 1'b1 ##0 d ##1 1'b1");
    test("b ##0 a[*0]", diag::SeqNoMatch);
    test("b ##0 a[*1]");
    test("a[*0] ##1 b");
    test("a ##1 b[*0] ##0 c");
    test("a ##1(b[*0] ##0 c)", diag::SeqNoMatch);

    test("(1 ##1 0)[*0]", diag::SeqNoMatch);
    test("(a[*0] ##1 a[*0])[*1]", diag::SeqEmptyMatch);
    test("(a[*0] ##2 a[*0])[*1]");
    test("not (a[*0] ##0 b)", diag::SeqNoMatch);
    test("not (a[*0] ##1 b)");

    test("(1'b1) intersect (##[1:3] 1'b1 ##0 1'b1[*0:3] ##[2:3] 1'b1[*1])", diag::SeqNoMatch);
    test("(1'b1) intersect (##[1:3] 1'b1 ##0 1'b1[*0:3] ##[2:3] 1'b1[*0])", diag::SeqNoMatch);
    test("(1'b1) intersect (##[0:3] 1'b1 ##1 1'b1[*0:2] ##[2:3] 1'b1[*0])", diag::SeqNoMatch);
    test("(1'b1) intersect (##[0:3] 1'b1[*0:2])");
    test("(1'b1) intersect (##[0:3] 1'b1[*0])");
    test("(1'b1) intersect (##[0:3] 1'b1)");
    test("(1'b1) intersect (1'b1[*0] ##[0:3] 1'b1)");
    test("(1'b1) intersect (1'b1[*0:2] ##[0:3] 1'b1)");
    test("(1'b1) intersect (1'b1 ##[1:3] 1'b1)", diag::SeqNoMatch);
    test("1[+] intersect (1'b1 ##5 1'b1)");
    test("(1'b1 ##4 1'b1) within (1'b1 ##1 1'b1)", diag::SeqNoMatch);
    test("1'b0 ##2 1'b1", diag::SeqNoMatch);
    test("1[*2]");
    test("1[*0]", diag::SeqEmptyMatch);
    test("1[*0:2]", diag::SeqEmptyMatch);
    test("1'b1");
    test("1'b0", diag::SeqNoMatch);

    test("1'b1 |=> 1");
    test("1'b0 |=> 1", diag::SeqNoMatch);
    test("1[*2] |=> 1");
    test("1[*0] |=> 1");
    test("1'b1 |-> 1");
    test("1'b0 |-> 1", diag::SeqNoMatch);
    test("1[*0] |-> 1", diag::SeqOnlyEmpty);
    test("1[*0:2] |-> 1");

    test("1'b1 #=# 1");
    test("1'b0 #=# 1", diag::SeqNoMatch);
    test("1[*2] #=# 1");
    test("1[*0] #=# 1");
    test("1'b1 #-# 1");
    test("1'b0 #-# 1", diag::SeqNoMatch);
    test("1[*0] #-# 1", diag::SeqOnlyEmpty);
    test("1[*0:2] #-# 1");

    test("first_match(a and b)");
    test("(first_match(a and b))[*0]", diag::SeqEmptyMatch);
    test("first_match(a and (b[*0] ##0 b))", diag::SeqNoMatch);
    test("@clk a ##1 b");
    test("@clk a[*0] ##0 b", diag::SeqNoMatch);
    test("strong(a ##1 b)");
    test("strong(a ##0 b[*0])", diag::SeqNoMatch);
    test("weak(a intersect b)");
    test("weak(a intersect ##2 b)", diag::SeqNoMatch);
    test("accept_on(b) sync_reject_on(c) sync_accept_on(d) reject_on(e) b ##1 c");
    test("accept_on(b) b intersect ##2 b", diag::SeqNoMatch);
    test("accept_on(b) ##2 b intersect ##2 b");
    test("accept_on(b) b[*0] ##0 b", diag::SeqNoMatch);

    test("if (b) a ##1 c else d ##1 e");
    test("if (1'b0) a ##1 c else d ##1 e");
    test("if (1'b1) a ##1 c else d ##1 e");
    test("if (a) b intersect ##2 b", diag::SeqNoMatch);
    test("if (a) ##2 b intersect ##2 b");
    test("case (b) 1, 2, 3: 1 ##1 b; 4: a and b; default: 1 |-> b; endcase");
    test("case (b) 1, 2, 3: 1 ##1 b; 4: a and b; default: 1[*0] |-> b; endcase",
         diag::SeqOnlyEmpty);
    test("disable iff (clk) a");
}

TEST_CASE("Sequence nondegeneracy tests 3") {
    auto test = [](std::string_view expr, std::optional<DiagCode> code = {}) {
        auto tree = SyntaxTree::fromText(fmt::format(R"(
module top;
    sequence s(int i);
        int j, k = j;
        {};
    endsequence

    assert property (s(1));
endmodule
)",
                                                     expr));
        Compilation compilation;
        compilation.addSyntaxTree(tree);

        auto& diags = compilation.getAllDiagnostics();
        if (!code) {
            CHECK(diags.empty());
            if (!diags.empty())
                FAIL_CHECK(expr);
        }
        else if (diags.size() != 1 || diags[0].code != code) {
            FAIL_CHECK(expr);
            CHECK(diags.size() == 1);
            if (diags.size() == 1)
                CHECK(diags[0].code == *code);
        }
    };

    test("(i == i, j = 1, j++)[*0:1]", diag::SeqEmptyMatch);
    test("(i != i, j = 1, j++)[*1:1]", diag::SeqNoMatch);
    test("(i != i, j = 1, j++)[*0:1]", diag::SeqNoMatch);
    test("(i == i, j = 1, j++)[*1:1]");
    test("(i == i, j = 1, j++)[*0:0]", diag::SeqEmptyMatch);
    test("(i == i, j = 1, j++)[*0]", diag::SeqEmptyMatch);
}

TEST_CASE("Sequence nondegeneracy tests 4") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic c, d;
    property p(logic i, foo = 1);
	    ##1 c ##1 d ##1 i;  // may be legal or not - depends on value of `i`
    endproperty

    assert property (p (0, 0));  // illegal
    assert property (p (1, 0));  // legal
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SeqNoMatch);
}

TEST_CASE("Sequence nondegeneracy tests 5") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk, reset, a, b;
    assert property(@(posedge clk) disable iff (reset)
        a |-> {500-$bits($past(b)){1'b0}} != 0);  // illegal

    assert property(@(posedge clk) disable iff (reset)
        {3 - 2{3'b111}} != 0);  // legal

    assert property(@(posedge clk) disable iff (reset)
        {500 - $bits(b){1'b1}} != 0);  // legal
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SeqNoMatch);
}

TEST_CASE("Sequence nondegeneracy tests 6") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic rstb;
    logic a;
    logic b;

    property p1(clk, rstb, a, b);
        @(posedge clk) disable iff(~rstb)
        $fell(a) |-> !$stable(b) within((~a)[*1:$] ##1 a);
    endproperty

    LABEL1: assert property(p1(clk, rstb, a, b));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Sequence local variable same as formal argument declaration") {
    auto tree = SyntaxTree::fromText(R"(
logic a, b, c;
int d;

sequence sub_seq(lv);
int lv;
(a ##1 !a, lv = 1) ##1 !b[*0:$] ##1 b && (1 == lv);
endsequence

sequence seq;
int v1;
c ##1 sub_seq(v1)
##1 (d == v1);
endsequence

module m;
    int m;
    assert property(seq);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::Redefinition);
}

TEST_CASE("Invalid property lookup crash regress") {
    auto tree = SyntaxTree::fromText(R"(
f(p1(,;property p1(,
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}

TEST_CASE("Explicit clocks specified in seq / prop in clocking block") {
    auto tree = SyntaxTree::fromText(R"(
module m(input clk, a);
    clocking cb @(posedge clk);
        sequence s;
            @(posedge clk) a;
        endsequence

        property p;
            @(posedge clk) a;
        endproperty
    endclocking
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExplicitClockInClockingBlock);
    CHECK(diags[1].code == diag::ExplicitClockInClockingBlock);
}

TEST_CASE("matched method can only be used in a sequence") {
    auto tree = SyntaxTree::fromText(R"(
module m(input clk, a);
    sequence s;
        @(posedge clk) a;
    endsequence

    always @(posedge clk) begin
        if (s.matched()) begin end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SequenceMatchedOutsideAssertion);
}

TEST_CASE("Assertion local var isn't rewritten") {
    auto tree = SyntaxTree::fromText(R"(
sequence s(local int a);
    (1, a++) ##1 1;
endsequence

module m(input clk);
    assert property (@(posedge clk) s(1));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assertion vacuity checking") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b;
    cover property (a |-> b);
    cover property (if (a) b);
    cover property (if (a) b else b);
    cover property (case (a) 0: b; 1: b; endcase);
    cover property (case (a) 0: b; 1: b; default: b; endcase);
    cover property (case (a) 0: b; 1: a |-> b; default: b; endcase);
    cover property (not (a |=> b));
    cover property (nexttime a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::VacuousCover);
    CHECK(diags[1].code == diag::VacuousCover);
    CHECK(diags[2].code == diag::VacuousCover);
    CHECK(diags[3].code == diag::VacuousCover);
    CHECK(diags[4].code == diag::VacuousCover);
    CHECK(diags[5].code == diag::VacuousCover);
}

TEST_CASE("Assertion instances in uninstantiated contexts -- GH #1512") {
    auto tree = SyntaxTree::fromText(R"(
module main
  (
   input wire clk,
   input wire reset
   );

   wire a;

   property delay (int CYCLES);
      @(posedge clk) disable iff (reset) ($past(a, CYCLES));
   endproperty

   localparam int TICKS = 0;

   if (TICKS < 0) begin: ticks_lt_zero
      $warning("Property was given: %0d", -TICKS);
      p: assume property (delay(-TICKS));
   end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Property expansion stack overflow regress") {
    auto tree = SyntaxTree::fromText(R"(
property p(o=o);
    1;
endproperty
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RecursiveDefinition);
}
