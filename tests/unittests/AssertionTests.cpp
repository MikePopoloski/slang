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
    CHECK(diags[7].code == diag::ValueMustBeIntegral);
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
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::AssertionArgTypeSequence);
    CHECK(diags[1].code == diag::AssertionArgTypeMismatch);
    CHECK(diags[2].code == diag::AssertionArgNeedsRegExpr);
}

TEST_CASE("Assertion instance arg expansion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [7:0] bar;

    assert property (s1($, 5));
    assert property (s1(bar, 9));

    sequence s1(a, int b);
        s2(a) ##1 bar[b:0];
    endsequence

    sequence s2(foo);
        1 ##[0:foo] 2 ##1 foo;
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UnboundedNotAllowed);
    CHECK(diags[1].code == diag::BadRangeExpression);
    CHECK(diags[2].code == diag::ConstEvalNonConstVariable);
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
