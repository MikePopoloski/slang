// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

TEST_CASE("Module ANSI ports") {
    auto tree = SyntaxTree::fromText(R"(
module mh0 (wire x); endmodule
module mh1 (integer x); endmodule
module mh2 (inout integer x); endmodule
module mh3 ([5:0] x); endmodule
module mh4 (var x); endmodule
module mh5 (input x); endmodule
module mh6 (input var x); endmodule
module mh7 (input var integer x); endmodule
module mh8 (output x); endmodule
module mh9 (output var x); endmodule
module mh10(output signed [5:0] x); endmodule
module mh11(output integer x); endmodule
module mh12(ref [5:0] x); endmodule
module mh13(ref x [5:0]); endmodule
module mh14(wire x, y[7:0]); endmodule
module mh15(integer x, signed [5:0] y); endmodule
module mh16([5:0] x, wire y); endmodule
module mh17(input var integer x, wire y); endmodule
module mh18(output var x, input y); endmodule
module mh19(output signed [5:0] x, integer y); endmodule
module mh20(ref [5:0] x, y); endmodule
module mh21(ref x [5:0], y); endmodule
module mh22(ref wire x); endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    auto& diags = compilation.getAllDiagnostics();

#define checkPort(moduleName, name, dir, nt, type)            \
    {                                                         \
        auto def = compilation.getRoot().find(moduleName);    \
        REQUIRE(def);                                         \
        auto& body = def->as<InstanceSymbol>().body;          \
        auto& port = body.findPort(name)->as<PortSymbol>();   \
        CHECK(port.direction == ArgumentDirection::dir);      \
        CHECK(port.getType().toString() == (type));           \
        if (nt) {                                             \
            auto& net = port.internalSymbol->as<NetSymbol>(); \
            CHECK(&net.netType == (nt));                      \
        }                                                     \
    };

    auto wire = &compilation.getWireNetType();

    checkPort("mh0", "x", InOut, wire, "logic");
    checkPort("mh1", "x", InOut, wire, "integer");
    checkPort("mh2", "x", InOut, wire, "integer");
    checkPort("mh3", "x", InOut, wire, "logic[5:0]");
    checkPort("mh4", "x", InOut, nullptr, "logic");
    checkPort("mh5", "x", In, wire, "logic");
    checkPort("mh6", "x", In, nullptr, "logic");
    checkPort("mh7", "x", In, nullptr, "integer");
    checkPort("mh8", "x", Out, wire, "logic");
    checkPort("mh9", "x", Out, nullptr, "logic");
    checkPort("mh10", "x", Out, wire, "logic signed[5:0]");
    checkPort("mh11", "x", Out, nullptr, "integer");
    checkPort("mh12", "x", Ref, nullptr, "logic[5:0]");
    checkPort("mh13", "x", Ref, nullptr, "logic$[5:0]");
    checkPort("mh14", "x", InOut, wire, "logic");
    checkPort("mh14", "y", InOut, wire, "logic$[7:0]");
    checkPort("mh15", "x", InOut, wire, "integer");
    checkPort("mh15", "y", InOut, wire, "logic signed[5:0]");
    checkPort("mh16", "x", InOut, wire, "logic[5:0]");
    checkPort("mh16", "y", InOut, wire, "logic");
    checkPort("mh17", "x", In, nullptr, "integer");
    checkPort("mh17", "y", In, wire, "logic");
    checkPort("mh18", "x", Out, nullptr, "logic");
    checkPort("mh18", "y", In, wire, "logic");
    checkPort("mh19", "x", Out, wire, "logic signed[5:0]");
    checkPort("mh19", "y", Out, nullptr, "integer");
    checkPort("mh20", "x", Ref, nullptr, "logic[5:0]");
    checkPort("mh20", "y", Ref, nullptr, "logic[5:0]");
    checkPort("mh21", "x", Ref, nullptr, "logic$[5:0]");
    checkPort("mh21", "y", Ref, nullptr, "logic");

    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InOutPortCannotBeVariable);
    CHECK(diags[1].code == diag::RefPortMustBeVariable);
}

#ifdef _MSC_VER
#    pragma warning(disable : 4127)
#endif

TEST_CASE("Module ANSI interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I; logic f; modport bar(input f); endinterface
interface J; endinterface
interface K; logic f; endinterface
module L; endmodule

parameter int I = 3;
typedef struct { logic f; } J;

module m0(I a[3], b, input c); endmodule
module m1(J j); endmodule
module m2(L l); endmodule
module m3(var K k, wire w); endmodule
module m4(output K k, output var v); endmodule
module m5(J.foo a1, K.f a2); endmodule
module m6(I.bar bar); endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto getPort = [&](std::string_view defName, std::string_view portName) {
        auto def = compilation.tryGetDefinition(defName, compilation.getRoot()).definition;
        REQUIRE(def);
        auto& inst = InstanceSymbol::createDefault(compilation, def->as<DefinitionSymbol>());
        return inst.body.findPort(portName);
    };

#define checkWirePort(moduleName, name, dir, nt, type)            \
    {                                                             \
        auto& port = getPort(moduleName, name)->as<PortSymbol>(); \
        CHECK(port.direction == ArgumentDirection::dir);          \
        CHECK(port.getType().toString() == (type));               \
        if (nt) {                                                 \
            auto& net = port.internalSymbol->as<NetSymbol>();     \
            CHECK(&net.netType == (nt));                          \
        }                                                         \
    };

#define checkIfacePort(moduleName, portName, ifaceName, modportName)           \
    {                                                                          \
        auto& port = getPort(moduleName, portName)->as<InterfacePortSymbol>(); \
        REQUIRE(port.interfaceDef);                                            \
        CHECK(port.interfaceDef->name == (ifaceName));                         \
        if (*(modportName)) {                                                  \
            CHECK(port.modport == (modportName));                              \
        }                                                                      \
        else {                                                                 \
            CHECK(port.modport.empty());                                       \
        }                                                                      \
    };

    auto wire = &compilation.getWireNetType();

    checkIfacePort("m0", "a", "I", "");
    checkIfacePort("m0", "b", "I", "");
    checkWirePort("m0", "c", In, wire, "logic");
    checkWirePort("m1", "j", InOut, wire, "J");
    checkIfacePort("m3", "k", "K", "");
    checkWirePort("m3", "w", InOut, wire, "logic");
    checkWirePort("m4", "v", Out, nullptr, "logic");
    checkIfacePort("m5", "a1", "J", "");
    checkIfacePort("m5", "a2", "K", "");
    checkIfacePort("m6", "bar", "I", "bar");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::PortTypeNotInterfaceOrData);
    CHECK(diags[1].code == diag::VarWithInterfacePort);
    CHECK(diags[2].code == diag::DirectionWithInterfacePort);
    CHECK(diags[3].code == diag::NotAModport);
    CHECK(diags[4].code == diag::NotAModport);
}

TEST_CASE("Module non-ANSI ports") {
    auto tree = SyntaxTree::fromText(R"(
module test(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r);
    inout a;
    inout a;            // Error, redefinition
    output a;           // Error, redefinition
    ref b;              // Error, net type can't be ref
    ref var c;
    inout logic d;      // Error, variable type can't be inout
    input wire e;
    ref wire f;         // Error, net type can't be ref

    input logic g;      // Error, collides with variable g below
    input h;
    output i;
    output j;           // Error, collides with parameter j below
    input unsigned k;   // Error, type isn't integral

    input l;
    input [2:0] m;
    input n[3];
    input o[3];         // Error, not all dimensions match
    input [2:0][3:1] p [1:2][2:0][5];
    input signed [2:0][3:1] q [1:2][2:0][5];
    input signed [2:0][3:1] r [1:2][2:0][5];    // Error, not all dimensions match

    logic g;
    struct { logic f; } h;
    wire [2:0] i;
    parameter int j = 1;
    struct { logic f; } k;

    logic [1:0] l [2];
    logic [2:0] m;
    logic n[3];
    logic [2:0] o[3];
    logic [2:0][3:1] p [1:2][2:0][5];
    logic [2:0][3:1] q [1:2][2:0][5];
    logic [2:0][3:2] r [1:2][2:0][5];

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto wire = &compilation.getWireNetType();

    checkPort("test", "a", InOut, wire, "logic");
    checkPort("test", "b", Ref, wire, "logic");
    checkPort("test", "c", Ref, nullptr, "logic");
    checkPort("test", "d", InOut, nullptr, "logic");
    checkPort("test", "e", In, wire, "logic");
    checkPort("test", "f", Ref, wire, "logic");

    checkPort("test", "g", In, nullptr, "logic");
    checkPort("test", "h", In, nullptr, "struct{logic f;}test.s$1");
    checkPort("test", "i", Out, wire, "logic[2:0]");
    checkPort("test", "j", Out, wire, "logic");
    checkPort("test", "k", In, nullptr, "struct{logic f;}test.s$2");
    checkPort("test", "l", In, nullptr, "logic[1:0]$[0:1]");
    checkPort("test", "m", In, nullptr, "logic[2:0]");
    checkPort("test", "n", In, nullptr, "logic$[0:2]");
    checkPort("test", "o", In, nullptr, "logic[2:0]$[0:2]");
    checkPort("test", "p", In, nullptr, "logic[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "q", In, nullptr, "logic signed[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "r", In, nullptr, "logic signed[2:0][3:2]$[1:2][2:0][0:4]");

    auto& diags = compilation.getAllDiagnostics();

    auto it = diags.begin();
    CHECK((it++)->code == diag::Redefinition);
    CHECK((it++)->code == diag::Redefinition);
    CHECK((it++)->code == diag::RefPortMustBeVariable);
    CHECK((it++)->code == diag::InOutPortCannotBeVariable);
    CHECK((it++)->code == diag::RefPortMustBeVariable);
    CHECK((it++)->code == diag::Redefinition);
    CHECK((it++)->code == diag::RedefinitionDifferentType);
    CHECK((it++)->code == diag::CantDeclarePortSigned);
    CHECK((it++)->code == diag::PortDeclDimensionsMismatch);
    CHECK(it == diags.end());
}

TEST_CASE("Module non-ANSI port signedness") {
    auto tree = SyntaxTree::fromText(R"(
module test(a,b,c,d,e,f,g,h);
    input [7:0] a;          // no explicit net declaration - net is unsigned
    input [7:0] b;
    input signed [7:0] c;
    input signed [7:0] d;   // no explicit net declaration - net is signed
    output [7:0] e;         // no explicit net declaration - net is unsigned
    output [7:0] f;
    output signed [7:0] g;
    output signed [7:0] h;  // no explicit net declaration - net is signed

    wire signed [7:0] b;    // port b inherits signed attribute from net decl.
    wire [7:0] c;           // net c inherits signed attribute from port
    logic signed [7:0] f;   // port f inherits signed attribute from logic decl.
    logic [7:0] g;          // logic g inherits signed attribute from port
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto wire = &compilation.getWireNetType();

    checkPort("test", "a", In, wire, "logic[7:0]");
    checkPort("test", "b", In, wire, "logic signed[7:0]");
    checkPort("test", "c", In, wire, "logic signed[7:0]");
    checkPort("test", "d", In, wire, "logic signed[7:0]");
    checkPort("test", "e", Out, wire, "logic[7:0]");
    checkPort("test", "f", Out, nullptr, "logic signed[7:0]");
    checkPort("test", "g", Out, nullptr, "logic signed[7:0]");
    checkPort("test", "h", Out, wire, "logic signed[7:0]");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Simple port connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input int a, b, c);
endmodule

module test;
    int foo;
    m m1(foo, bar(), 1 + 2);
    function int bar(); return 1; endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module port connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a, b, c);
endmodule

interface I #(parameter int foo = 1);
endinterface

interface J;
endinterface

module n(I i);
endmodule

module o(K.foo k);
endmodule

module p(I i[4]);
    localparam bar = i[0].foo;
endmodule

module q(I i[3][4]);
    p p1[3] (.*);
endmodule

module test;

    m m9(.*);               // used before declared
    m m10(.a, .b(0), .c(c));// used before declared

    logic a,b,c;

    m m1(1, 1, 1);
    m m2(1, , 1);
    m m3(1, 0);             // warning about unconnected
    m m4(1, .b());          // error: mixing
    m m5(.*, .a, .*);       // error: duplicate wildcard
    m m6(.a(), .b);         // warning about unconnected
    m m7(.a, .a());         // error: duplicate
    m m8(.a(1+0), .b, .c);

    I i();
    J j();

    n n1();                 // error: iface not assigned
    n n2(1);                // error: expression assigned to iface
    n n3(i);
    n n4(.*);
    n n5(.i);
    n n6(.i(((i))));
    n n7(.i(foobar));       // error: unknown
    n n8(.i(m1));           // error: not an interface
    n n9(.i(j));            // wrong interface type

    o o1(.k(i));            // early out, K is unknown

    I #(.foo(42)) i2[3][4] ();
    q q1(.i(i2));

    I i3[4][3] ();
    q q2(.i(i3));

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();

    auto it = diags.begin();
    CHECK((it++)->code == diag::UnknownInterface);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::MixingOrderedAndNamedPorts);
    CHECK((it++)->code == diag::DuplicateWildcardPortConnection);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::DuplicatePortConnection);
    CHECK((it++)->code == diag::InterfacePortNotConnected);
    CHECK((it++)->code == diag::InterfacePortInvalidExpression);
    CHECK((it++)->code == diag::NotAnInterface);
    CHECK((it++)->code == diag::NotAnInterface);
    CHECK((it++)->code == diag::InterfacePortTypeMismatch);
    CHECK((it++)->code == diag::PortConnDimensionsMismatch);
    CHECK(it == diags.end());

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("test.q1.p1[1].bar");
    CHECK(bar.getValue().integer() == 42);
}

TEST_CASE("Instance array port connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a[5]);
endmodule

module n(input logic c[3][4][5]);
endmodule

module o(input logic [1:0] d);
endmodule

module p(input logic e);
endmodule

module test;

    logic a[5];
    m m1(.a(a));

    logic b[3][4][5];
    m m2 [3][4] (.a(b));

    logic c[3][4][5];
    n n1 [1][9][3:0] (.c(c));

    logic [7:6][2:4] d [2][2:1];
    o o1 [1:0][2][3] (.d(d));

    logic [2:4][8:9][7:6] d2;
    o o2 [2:0][2] (.d(d2));

    logic e[3][4];
    p p1 [3][4] (.e(e));

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Instance array port connection errors") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a[5]);
endmodule

module n(input string c);
endmodule

module o(input logic [3:0] d);
endmodule

module test;

    logic b[3][4][5];
    m m1 [2][4] (.a(b));

    logic b2[2][4][4];
    m m2 [2][4] (.a(b2));

    string b3[2][4];
    m m3 [2][4][5] (.a(b3));

    string s;
    m m4 [2][4][5] (.a(s));

    logic [3:0] c;
    n n1 [2] (.c(c));

    logic [3:0][1:0][1:0] d;
    o o1 [2][4] (.d(d));

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::PortConnArrayMismatch);
    CHECK(diags[1].code == diag::PortConnArrayMismatch);
    CHECK(diags[2].code == diag::PortConnArrayMismatch);
    CHECK(diags[3].code == diag::BadAssignment);
    CHECK(diags[4].code == diag::PortConnArrayMismatch);
    CHECK(diags[5].code == diag::PortConnArrayMismatch);
}

TEST_CASE("Implicit interface ports") {
    auto tree = SyntaxTree::fromText(R"(
module n(input logic foo, I i);
endmodule

module test;
    I i1(), i();
    n n5(.foo(1), .i);
endmodule

interface I #(parameter int foo = 1);
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Malformed interface instance") {
    auto tree = SyntaxTree::fromText(R"(
module n(input logic foo, I i);
endmodule

module test;
    I i;
    n n5(.foo(1), .i);
endmodule

interface I #(parameter int foo = 1);
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InstanceMissingParens);
}

TEST_CASE("Instance array connection error reporting") {
    auto tree = SyntaxTree::fromText(R"(
module n #(parameter int count = 1) (input logic foo, I i[asdf-1:0]);
endmodule

module test #(parameter int count);
    I i[count-1:0] ();
    n #(.count(count)) n5(.foo(1), .i);
endmodule

interface I #(parameter int foo = 1);
endinterface

module top;
    test #(2) t1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Empty port connections") {
    auto tree = SyntaxTree::fromText(R"(
module n(input i, input j);
endmodule

module m;
    n n1(,);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Non-ANSI I/O lookup location") {
    auto tree = SyntaxTree::fromText(R"(
module m(a);
    input a;
    var integer c;
    initial c = a;
    integer a;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Modport conn mismatches") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    wire a, b;
    modport m(input a);
    modport n(input b);
endinterface

module m(I.m conn);
    n n1(conn);
    n n2(.conn);
endmodule

module n(I.n conn);
endmodule

module top;
    I i();
    m m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ModportConnMismatch);
    CHECK(diags[1].code == diag::ModportConnMismatch);
}

TEST_CASE("External modport connection") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    wire a, b;
    modport m(input a);
    modport n(input b);
endinterface

module m(I.m conn);
endmodule

module n(I.n conn);
endmodule

module o(I conn);
    m m2(conn);
    wire foo = conn.a;
endmodule

module top;
    I i();
    m m1(i.m);
    n n1(i.m); // error
    o o1(i.m);
    o o2(i.n); // error because of access inside o
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ModportConnMismatch);
    CHECK(diags[1].code == diag::InvalidModportAccess);
    CHECK(diags[2].code == diag::ModportConnMismatch);
}

TEST_CASE("Inconsistent port width regression") {
    auto tree = SyntaxTree::fromText(R"(
module counter(out, clk, reset);
  parameter WIDTH = 8;

  output [WIDTH-1 : 0] out;
  input clk, reset;

  reg [WIDTH-1 : 0] out;
  wire clk, reset;
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::LintMode;
    tree->isLibraryUnit = true;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Merged port initializer location") {
    auto tree = SyntaxTree::fromText(R"(
module m(out, in);
    output out;
    input in;
    wire out = in;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Empty non-ansi port") {
    auto tree = SyntaxTree::fromText(R"(
module m(,);
endmodule

module n;
    m m1(,);
    m m2(a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnconnectedUnnamedPort);
    CHECK(diags[1].code == diag::NullPortExpression);
}

TEST_CASE("Clocking blocks in modports") {
    auto tree = SyntaxTree::fromText(R"(
interface A_Bus( input logic clk );
    wire req, gnt;
    wire [7:0] addr, data;

    clocking sb @(posedge clk);
        input gnt;
        output req, addr;
        inout data;
        property p1; gnt ##[1:3] data; endproperty
    endclocking

    modport DUT ( input clk, req, addr,
                  output gnt,
                  inout data );

    modport STB ( clocking sb );

    modport TB ( input gnt,
                 output req, addr,
                 inout data );
endinterface

module dev1(A_Bus.DUT b);
endmodule

module dev2(A_Bus.DUT b);
endmodule

module top;
    logic clk;

    A_Bus b1( clk );
    A_Bus b2( clk );

    dev1 d1( b1 );
    dev2 d2( b2 );

    T tb( b1, b2 );
endmodule

program T (A_Bus.STB c, A_Bus.STB d);
    assert property (c.sb.p1);
    initial begin
        c.sb.req <= 1;
        wait( c.sb.gnt == 1 );

        c.sb.req <= 0;
        d.sb.req <= 1;
        wait( d.sb.gnt == 1 );

        d.sb.req <= 0;
    end
endprogram
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchical interface port connection") {
    auto tree = SyntaxTree::fromText(R"(
module Top();
    dut inst_0(inst1.intf_inst_1);
    dut inst_1(inst2.intf_inst_2);
    sub_1 inst1();
    sub_2 inst2();
endmodule

module dut(intf pi);
    parameter P = pi.P;
endmodule

module sub_1();
    intf #(3)intf_inst_1();
endmodule

module sub_2();
    intf #(4)intf_inst_2();
endmodule

interface intf();
    parameter P = 0;
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& p1 = compilation.getRoot().lookupName<ParameterSymbol>("Top.inst_0.P");
    CHECK(p1.getValue().integer() == 3);

    auto& p2 = compilation.getRoot().lookupName<ParameterSymbol>("Top.inst_1.P");
    CHECK(p2.getValue().integer() == 4);
}

TEST_CASE("Non-ansi interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I #(int foo);
    int baz;
    modport mod(input baz);
endinterface

module m;
    I #(5) i1();
    n n1(i1, i1);
endmodule

module n(x, y);
    I x;

    localparam bar = x.foo;
    wire integer i = y.baz;

    I.mod y;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.n1.bar");
    CHECK(bar.getValue().integer() == 5);
}

TEST_CASE("Non-ansi port errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int foo;
    modport mod(input foo);
endinterface

module m;
    I i2(), i3 [2] ();
    n n1(i1, i2, i3);
endmodule

module n(x, y, z);
    I.mod y;
    I y;
    I z[2];
    I z;
endmodule

module o(x);
    I x[foo];
endmodule

module p(x, {y, z, w});
    const ref int x;
    I y;
    I.mod z;
endmodule

module q({x, y}, {z, w}, {q, r});
    input foo x;
    input y, z, w[3];

    input [16777215-1:0] q, r;
endmodule

module r({x, y}, {z, w}, {q, r}, {o, p});
    inout x;
    output logic y;

    input logic z;
    inout w;

    ref int q;
    output r;

    input o;
    ref int p;
endmodule

module s(x, y, z, w, q, r[2]);
    input x = 1;
    output int y = foo;
    I z = 3;
    I.mod w = 3;

    int baz;
    output int q = baz;

    I r;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 21);
    CHECK(diags[0].code == diag::MissingPortIODeclaration);
    CHECK(diags[1].code == diag::Redefinition);
    CHECK(diags[2].code == diag::Redefinition);
    CHECK(diags[3].code == diag::UndeclaredIdentifier);
    CHECK(diags[4].code == diag::IfacePortInExpr);
    CHECK(diags[5].code == diag::IfacePortInExpr);
    CHECK(diags[6].code == diag::MissingPortIODeclaration);
    CHECK(diags[7].code == diag::ConstPortNotAllowed);
    CHECK(diags[8].code == diag::BadConcatExpression);
    CHECK(diags[9].code == diag::ValueExceedsMaxBitWidth);
    CHECK(diags[10].code == diag::UndeclaredIdentifier);
    CHECK(diags[11].code == diag::PortConcatInOut);
    CHECK(diags[12].code == diag::PortConcatInOut);
    CHECK(diags[13].code == diag::PortConcatRef);
    CHECK(diags[14].code == diag::PortConcatRef);
    CHECK(diags[15].code == diag::IfacePortInExpr);
    CHECK(diags[16].code == diag::DisallowedPortDefault);
    CHECK(diags[17].code == diag::UndeclaredIdentifier);
    CHECK(diags[18].code == diag::DisallowedPortDefault);
    CHECK(diags[19].code == diag::DisallowedPortDefault);
    CHECK(diags[20].code == diag::ConstEvalNonConstVariable);
}

TEST_CASE("Non-ansi port locations") {
    auto tree = SyntaxTree::fromText(R"(
module m(a, b);
    output a;
    input b;

    int i = 1;
    typedef int foo_t;

    localparam int j = 2;
    foo_t a = j;

    nettype int nt;
    nt #3 b;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("User-defined nettypes in ports") {
    auto tree = SyntaxTree::fromText(R"(
typedef logic[10:0] stuff[2];
nettype stuff baz;
nettype baz foo;

module m(x, y);
    input foo x;

    int baz[3];
    input foo y[$size(baz)];
endmodule

int bar[3];

module n(input foo x[$size(bar)], y);
endmodule

module top;
    foo f;
    foo g[3];
    m m1(f, g);
    n n1(g, f);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Non-ansi port expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m (a,a);
    input a;
endmodule

module n ({a, b}, a);
    input a;
    output b;
endmodule

module o (.a(i), .b(i), .c());
    inout i;
endmodule

module p (.a({b,c}), f, .g(h[1]), .i(foo[3:1]));
    input b,c,f,h[2];
    input logic [7:0] foo;
endmodule

module top;
    wire a;
    wire [1:0] b;

    m m1(a, a);
    n n1(b, 1);
    o o1(a, a, );
    o o2(.a, .b(a), .c());
    p p1(.a(b), .f(1), .g(b[0]), .i(3'd3));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface port modport inheritance") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    int j;
    modport m(input i);
endinterface

module m (I.m a, b);
    initial $display(a.i, a.j);
    initial $display(b.i, b.j);
endmodule

module n;
    I a();
    m m1(a, a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::InvalidModportAccess);
}

TEST_CASE("Generic interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    int j;
    modport m(input i);
    modport n(input j);
endinterface

interface J;
    int k;
endinterface

module m (interface a, b, interface.m c, d, e, interface.n f);
    initial $display(a.i, a.j);
    initial $display(b.i, b.j);
endmodule

module n;
    I i();
    J j();

    m m1(i, i.m, j, i, i.m, i.m);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::NotAModport);
    CHECK(diags[2].code == diag::ModportConnMismatch);
}

TEST_CASE("Explicit ansi ports") {
    auto tree = SyntaxTree::fromText(R"(
module m(input .a(), .b(foo[3:2]), .c(3'd3), output .d(3'd3), ref .e(bar), i);
    logic [4:0] foo;
    const int bar = 2;
endmodule

module top;
    logic [2:0] foo;
    int bar;
    logic i;
    m m1(.a(1), .b(2'd2), .c(), .d(foo), .e(bar), .i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
    CHECK(diags[1].code == diag::InvalidRefArg);
    CHECK(diags[2].code == diag::NullPortExpression);
}

TEST_CASE("Ansi port initializers") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
endinterface

int foo;
module m(input int i = 1, j = foo, output int k = 3, Iface iface = 4);
endmodule

module top;
    Iface iface();
    m m1(.iface);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[1].code == diag::AnsiIfacePortDefault);
    CHECK(diags[2].code == diag::UnconnectedNamedPort);
}

TEST_CASE("Implicit named port connection directions") {
    auto tree = SyntaxTree::fromText(R"(
module m(input int a, output int b, ref c);
endmodule

module top;
    localparam int a = 1;
    localparam int b = 2;
    wire c;
    m m1(.a, .b, .c);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::CantModifyConst);
    CHECK(diags[1].code == diag::InvalidRefArg);
}

TEST_CASE("No default nettype warning") {
    auto tree = SyntaxTree::fromText(R"(
`default_nettype none

module m(input i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImplicitNetPortNoDefault);
}

TEST_CASE("Module as interface port def") {
    auto tree = SyntaxTree::fromText(R"(
module N;
endmodule

module m (N n);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::PortTypeNotInterfaceOrData);
}

TEST_CASE("More port connection tests") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport mod (input i);
endinterface

module m(input int x = 3);
endmodule

module n({a, b}, c, d);
    input a,b,c;
    I d;
endmodule

module o(I i);
endmodule

module p({a, b});
    input a, b;
endmodule

module q(input r);
endmodule

module s(I y);
endmodule

module t(I z);
endmodule

module u(I z[3]);
endmodule

module v(input int qq);
endmodule

module w(t t);
endmodule

module asdf(a[2:1]);
    input logic [3:0] a;
endmodule

module top;
    I i();
    logic r;

    m m1();
    m m2(2, 3);
    m m3((* foo = 1 *));
    m m4((* foo = 2 *) .x);
    m m5((* foo = 3 *) .*);
    n n1(.c(0));
    o o1(.i(), .foo(2));
    o o2((* baz = 3 *) .i);
    o o3((* baz = 3 *) .i(i));
    p p1((* bar = 2 *));
    q q1((* baz = 4 *) .r);
    s s1(.y);
    t t1(.z);

    I z();
    I arr[foo]();

    u u1(.z(z.mod));
    u u2(.z(arr));

    logic signed [1:0] qq;
    v v1(.qq);

    w w1(t);

    asdf aa1(.a(3));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& m1 = compilation.getRoot().lookupName<InstanceSymbol>("top.m1");
    auto& m1_i = m1.body.findPort("x")->as<PortSymbol>();
    CHECK(!m1_i.getInternalExpr());
    CHECK(!m1.getPortConnection(m1_i)->getIfaceConn().first);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 15);
    CHECK(diags[0].code == diag::PortTypeNotInterfaceOrData);
    CHECK(diags[1].code == diag::TooManyPortConnections);
    CHECK(diags[2].code == diag::ImplicitNamedPortNotFound);
    CHECK(diags[3].code == diag::InterfacePortNotConnected);
    CHECK(diags[4].code == diag::UnconnectedUnnamedPort);
    CHECK(diags[5].code == diag::InterfacePortNotConnected);
    CHECK(diags[6].code == diag::PortDoesNotExist);
    CHECK(diags[7].code == diag::ImplicitNamedPortNotFound);
    CHECK(diags[8].code == diag::UsedBeforeDeclared);
    CHECK(diags[9].code == diag::UndeclaredIdentifier);
    CHECK(diags[10].code == diag::PortConnDimensionsMismatch);
    CHECK(diags[11].code == diag::ImplicitNamedPortTypeMismatch);
    CHECK(diags[12].code == diag::PortWidthExpand);
    CHECK(diags[13].code == diag::UnconnectedUnnamedPort);
    CHECK(diags[14].code == diag::PortDoesNotExist);
}

TEST_CASE("Inconsistent port collapsing") {
    auto tree = SyntaxTree::fromText(R"(
module m (input .a({b, {c[1:0], d}}), input uwire [2:1] f);
    wand b;
    wand [3:0] c;
    supply0 d;
endmodule

module n ({b[1:0], a});
    input tri0 a;
    input tri1 [3:0] b;
endmodule

module x(input trireg in);
    y y(.in);
    y y1(in);
    y y2(.in(in));
endmodule

module y(input wor in);
endmodule

module top;
    wand a;
    wor b;
    trireg [1:0] c;

    m m1({a, b, c}, c);
    n n1({{a, a}, c[0]});
    x x1(b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::ImplicitConnNetInconsistent);
    CHECK(diags[1].code == diag::NetInconsistent);
    CHECK(diags[2].code == diag::NetInconsistent);
    CHECK(diags[3].code == diag::NetRangeInconsistent);
    CHECK(diags[4].code == diag::NetRangeInconsistent);
    CHECK(diags[5].code == diag::NetInconsistent);
    CHECK(diags[6].code == diag::NetRangeInconsistent);
    CHECK(diags[7].code == diag::NetInconsistent);
}

TEST_CASE("Inout port conn to variable") {
    auto tree = SyntaxTree::fromText(R"(
module m(logic a);
endmodule

module top;
    logic a;
    m m1(a);
    m m2(.a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InOutVarPortConn);
    CHECK(diags[1].code == diag::InOutVarPortConn);
}

TEST_CASE("Unconnected ref port errors") {
    auto tree = SyntaxTree::fromText(R"(
module m(a[1:0]);
    ref int a;
endmodule

module n(ref int a);
endmodule

module top;
    m m1();
    n n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::RefPortUnnamedUnconnected);
    CHECK(diags[1].code == diag::RefPortUnconnected);
}

TEST_CASE("User-defined nettype port connection errors") {
    auto tree = SyntaxTree::fromText(R"(
nettype integer nt1;

module m(nt1 foo, bar, input nt1 baz);
endmodule

module n(input signed foo);
endmodule

module o(nt1 a);
endmodule

module p({a, b});
    input nt1 a, b;
endmodule

module top;
    wire signed [5:0] a;
    wire integer b;

    m m1(a, b, b);

    nettype logic signed[5:0] nt2;
    nt2 c;
    n n1(c);

    o o1(c);

    p p1({c, c});

    nt1 d;
    p p2({d, d});
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::MismatchedUserDefPortConn);
    CHECK(diags[1].code == diag::PortWidthTruncate);
    CHECK(diags[2].code == diag::MismatchedUserDefPortDir);
    CHECK(diags[3].code == diag::MismatchedUserDefPortConn);
    CHECK(diags[4].code == diag::PortWidthTruncate);
    CHECK(diags[5].code == diag::UserDefPortTwoSided);
    CHECK(diags[6].code == diag::PortWidthTruncate);
    CHECK(diags[7].code == diag::UserDefPortMixedConcat);
    CHECK(diags[8].code == diag::PortWidthExpand);
}

TEST_CASE("inout uwire port errors") {
    auto tree = SyntaxTree::fromText(R"(
module m(a);
    inout uwire a;
endmodule

module n(inout uwire a);
endmodule

module p({a,b});
    inout a;
    input uwire b;
endmodule

module q(a);
    inout a;
endmodule

module top;
    uwire a;
    q q1(a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InOutUWirePort);
    CHECK(diags[1].code == diag::InOutUWirePort);
    CHECK(diags[2].code == diag::PortConcatInOut);
    CHECK(diags[3].code == diag::InOutUWireConn);
}

TEST_CASE("Assigning to input ports") {
    auto tree = SyntaxTree::fromText(R"(
module m(input .a(a), input int b, output int c);
    int a;
    assign a = 1;
    assign b = 2;
endmodule

module n(a[1:0]);
    input var [3:0] a;
    assign a[2:1] = 1;
    assign a[3] = 1;
endmodule

module o;
    int a, b, c = 1;
    m m1(.a, .b, .c);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InputPortAssign);
    CHECK(diags[1].code == diag::InputPortAssign);
    CHECK(diags[2].code == diag::InputPortAssign);
    CHECK(diags[3].code == diag::MixedVarAssigns);
}

TEST_CASE("Net port coercion") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    wire in1, out1;
    m m(in1, out1);
    assign out1 = 1'b1;
endmodule

module m (in1, out1);
    input in1;
    output out1;        // out1 is driven outside the module and thus used as an input
    assign in1 = 1'b0 ; // in1 is driven within the module and thus used as an output
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::OutputPortCoercion);
    CHECK(diags[1].code == diag::InputPortCoercion);
}

TEST_CASE("Interconnect ports") {
    auto tree = SyntaxTree::fromText(R"(
module m(interconnect a, b = 1);
endmodule

module n(a);
    input signed a;
    interconnect a;
endmodule

module netlist;
    interconnect iwire;
    dut1 child1(iwire);
    dut2 child2(iwire);
endmodule

module dut1(inout wire w);
    assign w = 1;
endmodule

module dut2(inout wand w);
    assign w = 0;
endmodule

module o({a, b});
    input interconnect a;
    input b;
endmodule

module p(input interconnect a);
endmodule

module q(input int b);
endmodule

module top;
    logic a;
    p p1(.a);

    interconnect b;
    q q1(.b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::InterconnectInitializer);
    CHECK(diags[1].code == diag::InterconnectTypeSyntax);
    CHECK(diags[2].code == diag::InterconnectMultiPort);
    CHECK(diags[3].code == diag::InterconnectPortVar);
    CHECK(diags[4].code == diag::InterconnectReference);
}

TEST_CASE("More interconnect ports") {
    auto tree = SyntaxTree::fromText(R"(
module top();
    interconnect [0:3] [0:1] aBus;
    logic [0:3] dBus;
    driver driverArray[0:3](aBus);
    cmp cmpArray[0:3](aBus,rst,dBus);
endmodule : top

package NetsPkg;
    nettype real realNet;
endpackage : NetsPkg

module driver
    import NetsPkg::*;
    #(parameter int delay = 30,
                int iterations = 256)
    (output realNet out [0:1]);
    timeunit 1ns / 1ps;
    real outR[1:0];
    assign out = outR;
    initial begin
        outR[0] = 0.0;
        outR[1] = 3.3;
        for (int i = 0; i < iterations; i++) begin
            #delay outR[0] += 0.2;
            outR[1] -= 0.2;
        end
    end
endmodule : driver

module cmp
    import NetsPkg::*;
    #(parameter real hyst = 0.65)
    (input realNet inA [0:1],
     input logic rst,
     output logic out);
    timeunit 1ns / 1ps;
    real updatePeriod = 100.0;

    initial out = 1'b0;

    always #updatePeriod begin
        if (rst) out <= 1'b0;
        else if (inA[0] > inA[1]) out <= 1'b1;
        else if (inA[0] < inA[1] - hyst) out <= 1'b0;
    end
endmodule : cmp
)");

    CompilationOptions options;
    options.defaultTimeScale = TimeScale();

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Implicit port connection with instance array slicing") {
    auto tree = SyntaxTree::fromText(R"(
module M(
    input logic a,
    output logic b
);
endmodule

module top;
    localparam N = 8;

    logic [N-1:0] a;
    logic [N-1:0] b;

    M m [N-1:0] (
        .a,
        .b
    );
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface array port with modport selector passthrough") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic i;
    modport m(input i);
endinterface

module top;
    I i();

    m m1(i.m);
endmodule

module m (I.m p1);
    n n1(.p1);
endmodule

module n (I.m p1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Non-ansi iface port crash regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I(.;input interface I
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // No crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Inout ports are treated as readers and writers") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    wire integer i;
    modport m(inout i);
endinterface

module m(inout wire a);
    wire local_a;
    pullup(local_a);
    tranif1(a, local_a, 1'b1);
endmodule

module top;
    I i();

    wire a;
    m m1(.*);
    m m2(.*);
endmodule
)");

    CompilationOptions options;
    options.flags &= ~CompilationFlags::SuppressUnused;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Ansi duplicate port compatibility option") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, output b);
    wire [31:0] a;
    logic [31:0] b;
    assign b = a;
endmodule

module top;
    logic [31:0] a, b;
    m m1(.a, .b);
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowMergingAnsiPorts;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Allow use before declare with wildcard connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a);
endmodule

module n;
    m m1(.*);
    logic a;
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowUseBeforeDeclare;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
