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
        p ? : ? : 0 ;
        n ? : ? : - ;
        ? n : ? : 0 ;
        ? p : ? : 0 ;
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
    pmos #3 asdf [3:0][4][5] (foo, 1, 0), blah (foo, 1, 0), (foo, 1, 0);
    rtranif1 (foo, foo, 1), asdf2(foo, foo, 0);

    pmos #6 (a, b, c);

    and (a, 1, 0, 1, 0, 0, 0, 1, 0);
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

primitive p15 (a, b);
    output a;
    input b;
    table
        0:0;
        0:1;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 26);
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
    CHECK(diags[22].code == diag::UdpCoverage);
    CHECK(diags[23].code == diag::UdpDupDiffOutput);
    CHECK(diags[24].code == diag::UdpAllX);
    CHECK(diags[25].code == diag::UdpDupDiffOutput);
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
    REQUIRE(diags.size() == 13);
    CHECK(diags[0].code == diag::UdpCoverage);
    CHECK(diags[1].code == diag::UdpInvalidSymbol);
    CHECK(diags[2].code == diag::UdpInvalidTransition);
    CHECK(diags[3].code == diag::UdpInvalidEdgeSymbol);
    CHECK(diags[4].code == diag::UdpTransitionLength);
    CHECK(diags[5].code == diag::UdpSingleChar);
    CHECK(diags[6].code == diag::UdpInvalidInputOnly);
    CHECK(diags[7].code == diag::UdpInvalidMinus);
    CHECK(diags[8].code == diag::UdpInvalidMinus);
    CHECK(diags[9].code == diag::UdpInvalidOutput);
    CHECK(diags[10].code == diag::UdpDupTransition);
    CHECK(diags[11].code == diag::UdpSequentialState);
    CHECK(diags[12].code == diag::UdpCombState);
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
         (??) : ? : -;
   endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Primitive with large number of inputs") {
    auto tree = SyntaxTree::fromText(R"(
 primitive p(output o, input i0, i1, i2, i3, i4, i5, i6, i7,
                             i8, i9, i10, i11, i12, i13, i14,
                             i15, i16, i17, i18, i19, i20);
   table
     bbbbbbbbbbbbbbbbbbbbb:1;
   endtable
 endprimitive

 module top;
   p p1(o, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10,
           i11, i12, i13, i14, i15, i16, i17, i18, i19, i20);
 endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("More UDP overlapping row errors") {
    auto tree = SyntaxTree::fromText(R"(
primitive p(output reg o, input a, b);
  table
    *x:1:1;
    (x1)1:1:0;
    p1:1:x;
    (x0)1:1:1;
    *?:1:0;
    n1:1:0;
    ?*:1:0;
  endtable
endprimitive

primitive pp (q, clock, data);
  output q; reg q;
  input clock, data;
  table
    // clock data q q+
    p ? : ? : 1 ;
    (x1) ? : ? : 0;
    n ? : ? : 1 ;
    (1x) ? : ? : 0;
    ? (??) : ? : - ;
  endtable
endprimitive

primitive ppp (q, clock, data);
  output q; reg q;
  input clock, data;
  table
    // clock data q q+
    (?0) ? : ? : 1 ;
    (0?) ? : ? : 1 ;
    (01) ? : ? : 0 ;
    (??) ? : ? : - ;
    ? (??) : ? : - ;
  endtable
endprimitive

module top;
  p p1(o, a, b);
  pp pp1(o, a, b);
  ppp ppp1(o, a, b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::UdpDupDiffOutput);
    CHECK(diags[1].code == diag::UdpDupDiffOutput);
    CHECK(diags[2].code == diag::UdpDupDiffOutput);
    CHECK(diags[3].code == diag::UdpDupDiffOutput);
    CHECK(diags[4].code == diag::UdpDupDiffOutput);
    CHECK(diags[5].code == diag::UdpDupDiffOutput);
}

TEST_CASE("UDP overlapping inputs with compatible outputs") {
    auto tree = SyntaxTree::fromText(R"(
 primitive X1 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : ?   :  0;
    *    0   : 0   :  -;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
 primitive X2 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : 1   :  -;
    *    0   : ?   :  1;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
 primitive X3 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : ?   :  -;
    *    0   : ?   :  0;
    *    1   : ?   :  0;
    r    1   : ?   :  -;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
 primitive X4 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : ?   :  -;
    *    0   : ?   :  1;
    *    1   : ?   :  1;
    r    1   : ?   :  -;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
 primitive X5 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : ?   :  -;
    *    0   : ?   :  x;
    *    1   : ?   :  x;
    r    1   : ?   :  -;
    *    ?   : b   :  x;
    ?    *   : b   :  -;
    endtable
 endprimitive
 primitive X6 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : b   :  -;
    *    0   : ?   :  0;
    *    1   : ?   :  0;
    r    1   : b   :  -;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
primitive X7 (q, clk, d);
    output reg q;
    input clk, d;
    table
    // clk in  : Qt  : Qt+1
    r    0   : b   :  -;
    *    0   : ?   :  1;
    *    1   : ?   :  1;
    r    1   : b   :  -;
    *    ?   : b   :  -;
    ?    *   : b   :  -;
    endtable
 endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 0);
}

TEST_CASE("More UDP error cases") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1(output reg o, input a);
  table
    (11):1:1;
  endtable
endprimitive

primitive p2(output o, input a);
  table
    p:1;
    1:-;
  endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UdpCoverage);
    CHECK(diags[1].code == diag::UdpTransSameChar);
    CHECK(diags[2].code == diag::UdpCoverage);
    CHECK(diags[3].code == diag::UdpEdgeInComb);
    CHECK(diags[4].code == diag::UdpInvalidMinus);
}

TEST_CASE("Most gates can't attach to user-defined nettypes") {
    auto tree = SyntaxTree::fromText(R"(
primitive p(output o, input i);
	table
      1 : 1;
    endtable
endprimitive

module m;
    nettype real ntr;
    nettype shortreal nts;

    ntr r1, r2;
    rtranif1(r1, r2, 1);

    ntr r3;
    and(r3, 1);

    ntr r4;
    p p1(r4, 1);

    // This one is allowed.
    ntr r5, r6;
    tranif1(r5, r6, 1);

    ntr r7;
    wire r8;
    tran(r7, r8);

    ntr r9;
    nts r10;
    tranif0(r9, r10, 0);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::GateUDNTConn);
    CHECK(diags[1].code == diag::GateUDNTConn);
    CHECK(diags[2].code == diag::GateUDNTConn);
    CHECK(diags[3].code == diag::GateUDNTConn);
    CHECK(diags[4].code == diag::BiDiSwitchNetTypes);
    CHECK(diags[5].code == diag::BiDiSwitchNetTypes);
}

TEST_CASE("UDP edge-sequence coverage no-error tests") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (q, clock, data);
    output q; reg q;
    input clock, data;
    table
        // clock data q q+
        (01) ? : ? : 0 ;
        (??) ? : ? : 0 ;
        ? (??) : ? : 0 ;
    endtable
endprimitive
primitive p2 (q, clock, data, data1);
output q; reg q;
    input clock, data, data1;
    table
        // clock data q q+
        n ? 1    : ? : 0 ;
        p ? 1    : ? : 0 ;
        n ? ?    : ? : 0 ;
        p ? ?    : ? : 0 ;
        ? (??) ? : ? : 0 ;
        ? ? (??) : ? : 0 ;
    endtable
endprimitive
primitive p3 (q, clock, data);
    output q; reg q;
    input clock, data;
    table
        // clock data q q+
        (??) ? : ? : 0 ;
        ? (??) : ? : 0 ;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("UDP edge-sequence coverage error tests") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (q, clock, data);
    output q; reg q;
    input clock, data;
    table
        // clock data q q+
        (01) ? : ? : 0 ;
    endtable
endprimitive
primitive p2 (q, clock, data, data1);
    output q; reg q;
    input clock, data, data1;
    table
        // clock data q q+
        n ? 1 : ? : 0 ;
        p ? 1 : ? : 0 ;
    endtable
endprimitive
primitive p3 (q, clock, data);
    output q; reg q;
    input clock, data;
    table
        // clock data q q+
        (??) ? : ? : 0 ;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UdpCoverage);
    CHECK(diags[1].code == diag::UdpCoverage);
    CHECK(diags[2].code == diag::UdpCoverage);
}

TEST_CASE("UDP with many inputs -- coverage checking") {
    auto tree = SyntaxTree::fromText(R"(
primitive p13 (output reg a, input b, c,d,e,f,g,h,i,j,k,l,m,n);
    table
        0(10)00000000000:0:0;
    endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UdpCoverage);
}
