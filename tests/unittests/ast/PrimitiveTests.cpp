// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

TEST_CASE("user-defined primitives") {
    auto tree = SyntaxTree::fromText(R"(
primitive srff (q, s, r);
    output q; reg q;
    input s, r;
    initial q = 1'b1;
    table
        // s r q q+
        1 0 : ? : 1 ;
        f 0 : 1 : - ;
        0 r : ? : 0 ;
        0 f : 0 : - ;
        1 1 : ? : 0 ;
    endtable
endprimitive : srff

primitive p2 (output reg a = 1'bx, input b, input c);
    table 00:0:0; endtable
endprimitive

module m;
    logic q;
    srff sf1(q, 1, 0);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Gates") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire foo;
    pullup (supply0, pull1) (foo);
    pmos #3 asdf [3:0][4][5] (foo, 2, 3), blah (foo, 4, 5), (foo, 5, 6);
    rtranif1 (foo, foo, 1), asdf2(foo, foo, 2);

    pmos #6 (a, b, c);

    and (a, 1, 2, 3, 4, 5, 6, 7, 8);
    buf (a, b, c, 1);

    logic [3:0] out, in, en;
    bufif0 ar[3:0] (out, in, en);

    wire [7:0] value1;
    wire [7:0] value2;
    cmos buffer[7:0](value2, value1, 1'b1, 1'b0);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("UDP errors") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (input a, b, output c);
    output b;
    table 00:0; endtable
endprimitive

primitive p1 (output a, input b);
    table 0:0; endtable
endprimitive

primitive p2 (output a);
    table 00:0; endtable
endprimitive

primitive p3 (a, b);
    input b;
    output a;
    output reg a;
    table 0:0:0; endtable
endprimitive

primitive p4 (a, b);
    input b;
    output a;
    reg a;
    reg a;
    input c;
    output d;
    table 0:0:0; endtable
endprimitive

primitive p5 (a, b);
    reg a;
    input b;
    output reg a;
    table 0:0:0; endtable
endprimitive

primitive p6 (a, b, c);
    input b;
    output a;
    reg b;
    table 00:0:0; endtable
endprimitive

primitive p7 (a, b, c);
    output b;
    output a;
    initial a = 1;
    table 00:0; endtable
endprimitive

primitive p8 (a, b);
    output reg a = 1;
    input b;
    initial a = 1'bx;
    table 0:0:0; endtable
endprimitive

primitive p9 (a, b);
    output reg a;
    input b;
    initial c = 1'bx;
    table 0:0:0; endtable
endprimitive

primitive p10 (a, b);
    output reg a;
    input b;
    initial a = 3;
    table 0:0:0; endtable
endprimitive

module p10; endmodule

module m;
endmodule

primitive m(output a, input b);
    table 0:0; endtable
endprimitive

primitive p11 (a, b);
    output reg a;
    input b;
    initial a = 1'b1;
    table 0: endtable
endprimitive

primitive p12 (a, b, c);
    output reg a;
    input b, c;
    table
        000:0:0;
        0:0:0;
    endtable
endprimitive

primitive p13 (a, b, c);
    output reg a;
    input b, c;
    table
        0(10):0:0;
        0f:0:1;
    endtable
endprimitive

primitive p14 (a, b, c);
    output reg a;
    input b, c;
    table
        xx:0:0;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 24);
    CHECK(diags[0].code == diag::PrimitiveOutputFirst);
    CHECK(diags[1].code == diag::PrimitiveAnsiMix);
    CHECK(diags[2].code == diag::DuplicateDefinition);
    CHECK(diags[3].code == diag::PrimitiveTwoPorts);
    CHECK(diags[4].code == diag::PrimitivePortDup);
    CHECK(diags[5].code == diag::PrimitiveRegDup);
    CHECK(diags[6].code == diag::PrimitivePortUnknown);
    CHECK(diags[7].code == diag::PrimitivePortUnknown);
    CHECK(diags[8].code == diag::PrimitivePortDup);
    CHECK(diags[9].code == diag::PrimitivePortMissing);
    CHECK(diags[10].code == diag::PrimitiveRegInput);
    CHECK(diags[11].code == diag::PrimitivePortMissing);
    CHECK(diags[12].code == diag::PrimitiveDupOutput);
    CHECK(diags[13].code == diag::PrimitiveInitialInComb);
    CHECK(diags[14].code == diag::PrimitiveDupInitial);
    CHECK(diags[15].code == diag::PrimitiveWrongInitial);
    CHECK(diags[16].code == diag::PrimitiveInitVal);
    CHECK(diags[17].code == diag::Redefinition);
    CHECK(diags[18].code == diag::Redefinition);
    CHECK(diags[19].code == diag::ExpectedUdpSymbol);
    CHECK(diags[20].code == diag::UdpWrongInputCount);
    CHECK(diags[21].code == diag::UdpWrongInputCount);
    CHECK(diags[22].code == diag::UdpDupDiffOutput);
    CHECK(diags[23].code == diag::UdpAllX);
}

TEST_CASE("UDP instances error checking") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (output a, input b);
    table 0:0; endtable
endprimitive

module m;
    logic foo[3];
    p1 #(3, 4) (a, b);
    p1 #(foo) (a, b);
    p1 #(.baz(1), .bar(2)) (a, b);
    p1 #(3, 4, 5) (a, b);
    p1 #3 (a, b);
    p1 (supply0, strong1) #(1:2:3, 3:2:1) asdf(a, b);
    p1 (,);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::DelayNotNumeric);
    CHECK(diags[1].code == diag::ExpectedNetDelay);
    CHECK(diags[2].code == diag::Delay3UdpNotAllowed);
    CHECK(diags[3].code == diag::EmptyUdpPort);
    CHECK(diags[4].code == diag::EmptyUdpPort);
}

TEST_CASE("Module mixup with primitive instance") {
    auto tree = SyntaxTree::fromText(R"(
module n;
endmodule

module m;
    n #  3 n1();
    n (supply0, strong1) n2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InstanceWithDelay);
    CHECK(diags[1].code == diag::InstanceWithStrength);
}

TEST_CASE("Module escaped name instead of primitive") {
    auto tree = SyntaxTree::fromText(R"(
module \and (output a, input b, c);
endmodule

module m;
    \and a(a1, b1, c1);
    and (a2, b2, c2);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("UDP body errors") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (q, s, r);
    output q; reg q;
    input s, r;
    initial q = 1'b1;
    table
        // s r q q+
        zx : (10) : 1 ;
        f 0 : 1 : - ;
        (1r) x : ? : 0 ;
        (111) x : 0 : - ;
        1 1 : ? : 01 ;
        1 1 : * : 1;
        1 - : 0 : 1;
        1 1 : - : 1;
        1 1 : 1 : ?;
        rr : 1 : 1;
        1 1 : 1;
    endtable
endprimitive

primitive p2 (q, s, r);
    output q;
    input s, r;
    table
        1 1 : 1 : 1;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 12);
    CHECK(diags[0].code == diag::UdpInvalidSymbol);
    CHECK(diags[1].code == diag::UdpInvalidTransition);
    CHECK(diags[2].code == diag::UdpInvalidEdgeSymbol);
    CHECK(diags[3].code == diag::UdpTransitionLength);
    CHECK(diags[4].code == diag::UdpSingleChar);
    CHECK(diags[5].code == diag::UdpInvalidInputOnly);
    CHECK(diags[6].code == diag::UdpInvalidMinus);
    CHECK(diags[7].code == diag::UdpInvalidMinus);
    CHECK(diags[8].code == diag::UdpInvalidOutput);
    CHECK(diags[9].code == diag::UdpDupTransition);
    CHECK(diags[10].code == diag::UdpSequentialState);
    CHECK(diags[11].code == diag::UdpCombState);
}

TEST_CASE("UDP row error checking regress") {
    auto tree = SyntaxTree::fromText(R"(
module test;
   wire q, e;
   reg  a, b;
   drec #1 rec(q, a, b);
   edet det (e, q);

   reg	error;
   initial
     begin
	error = 0;
	#2;
	forever @(e)
	  if (e !== 1'bx) begin
	     error = 1;
	     $display("%0d: FAILED: e=%b", $time, e);
	  end
     end

   always @(q)
     $display("%d: q=%b", $time, q);

   initial
     begin
	a = 0;
	b = 1;
	#3;
	a = 1;
	b = 0;
	#2;
	a = 0;
	b = 1;
	#3;
	if (!error)
	  $display("PASSED");
     end
endmodule

primitive drec (q, a, b);
   output        q;
   input  a, b;
   table
          1  0 : 1 ;
          0  1 : 0 ;
   endtable
endprimitive

primitive edet (q, i);
   output           q;
   input  i;
   reg	        q;
   table
         (?x) : ? : 1;
         (x?) : ? : 0;
   endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
