#include "Test.h"

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
    int b,c,d,e;

    foo: assert property (a);
    assert property (a ##1 b ##[+] c ##[*] d ##[1:5] e);
    assert property (##0 a[*0:4] ##0 b[=4] ##0 c[->1:2] ##0 c[*] ##1 d[+]);
    assert property (##[0:$] a[*0:$]);
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
    assert property (if (b) a ##1 c else d ##1 e);
    assert property (case (b) 1, 2, 3: 1 ##1 b; 4: a and b; default: 1 |-> b; endcase);
    assert property (@(posedge b) ((b) and b) ##0 b);
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
    int b;
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
    CHECK(diags[8].code == diag::InvalidSequenceRange);
    CHECK(diags[9].code == diag::ExpectedExpression);
    CHECK(diags[10].code == diag::ExpectedExpression);
    CHECK(diags[11].code == diag::InvalidSequenceRange);
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

    int c, d;
    sequence b;
        ##1 c ##1 d;
    endsequence
endmodule

module n;
    int c, d;
    property a(int i, foo = 1);
        ##1 c ##1 d ##1 i;
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
    assert property (a(1, 1 iff 2, foo, 1 and 2));
    assert property (a(1 iff 2, 1, 1));
    assert property (a(1, 1, foo[*]));

    int e;
    sequence a(sequence a, property b, int c[], untyped d = e);
        1;
    endsequence

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
    assert property (s3(9));
    assert property (s4(1 and 2));

    sequence s1(a, int b);
        s2(a) ##1 bar[b:0];
    endsequence

    sequence s2(foo);
        1 ##[0:foo] 2 ##1 foo;
    endsequence

    sequence s3(sequence a);
        1 ##[0:a] 2;
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
    CHECK(diags[1].code == diag::BadRangeExpression);
    CHECK(diags[2].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[3].code == diag::ExprMustBeIntegral);
    CHECK(diags[4].code == diag::BadBinaryExpression);
}

TEST_CASE("More complex sequence arg expansion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s1;
        int foo;
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
    default disable iff a;
    default disable iff b;
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
        (i && j, j = 1, j++)[*0:1];
    endsequence

    int baz;
    sequence s2;
        int j, k = j;
        first_match(j, !j, j + k, baz = 1, baz++);
    endsequence

    typedef int Foo;
    property p;
        Foo u, v;
        s(u) and v and s2;
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

TEST_CASE("Sequence triggered method") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk, ready;
    sequence e1;
        @(posedge clk) $rose(ready) ##1 1 ##1 2;
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
            |-> (data == expected_data[i*8+:8])
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

module m;
    assert property (check_write);
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

module m;
    logic clk;

    cover property (event_arg_example(clk));
    cover property (event_arg_example(posedge clk));
    cover property (event_arg_example((posedge clk iff x or edge clk, x iff y, negedge clk)));
    cover property (event_arg_example((x iff y, negedge clk)));
    cover property (event_arg_example(((x iff y) or negedge clk)));
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

    assert property (s1((x and y) iff clk));
    assert property (s1((x and y)[*0:1]));
    assert property (s1(x[*0:1]));
    assert property (s1(x |-> y));
    assert property (s1(x throughout y));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::InvalidMatchItem);
    CHECK(diags[1].code == diag::InvalidSignalEventInSeq);
    CHECK(diags[2].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[3].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[4].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[5].code == diag::InvalidSyntaxInEventExpr);
    CHECK(diags[6].code == diag::InvalidSyntaxInEventExpr);
}
