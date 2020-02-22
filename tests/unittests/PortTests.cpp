#include "Test.h"

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

#define checkPort(moduleName, name, dir, nt, type)                 \
    {                                                              \
        auto def = compilation.getDefinition(moduleName);          \
        REQUIRE(def);                                              \
        auto& port = def->getPortMap().at(name)->as<PortSymbol>(); \
        CHECK(port.direction == (dir));                            \
        CHECK(port.getType().toString() == (type));                \
        if (nt) {                                                  \
            auto& net = port.internalSymbol->as<NetSymbol>();      \
            CHECK(&net.netType == (nt));                           \
        }                                                          \
    };

    auto wire = &compilation.getWireNetType();

    checkPort("mh0", "x", PortDirection::InOut, wire, "logic");
    checkPort("mh1", "x", PortDirection::InOut, wire, "integer");
    checkPort("mh2", "x", PortDirection::InOut, wire, "integer");
    checkPort("mh3", "x", PortDirection::InOut, wire, "logic[5:0]");
    checkPort("mh4", "x", PortDirection::InOut, nullptr, "logic");
    checkPort("mh5", "x", PortDirection::In, wire, "logic");
    checkPort("mh6", "x", PortDirection::In, nullptr, "logic");
    checkPort("mh7", "x", PortDirection::In, nullptr, "integer");
    checkPort("mh8", "x", PortDirection::Out, wire, "logic");
    checkPort("mh9", "x", PortDirection::Out, nullptr, "logic");
    checkPort("mh10", "x", PortDirection::Out, wire, "logic signed[5:0]");
    checkPort("mh11", "x", PortDirection::Out, nullptr, "integer");
    checkPort("mh12", "x", PortDirection::Ref, nullptr, "logic[5:0]");
    checkPort("mh13", "x", PortDirection::Ref, nullptr, "logic$[5:0]");
    checkPort("mh14", "x", PortDirection::InOut, wire, "logic");
    checkPort("mh14", "y", PortDirection::InOut, wire, "logic$[7:0]");
    checkPort("mh15", "x", PortDirection::InOut, wire, "integer");
    checkPort("mh15", "y", PortDirection::InOut, wire, "logic signed[5:0]");
    checkPort("mh16", "x", PortDirection::InOut, wire, "logic[5:0]");
    checkPort("mh16", "y", PortDirection::InOut, wire, "logic");
    checkPort("mh17", "x", PortDirection::In, nullptr, "integer");
    checkPort("mh17", "y", PortDirection::In, wire, "logic");
    checkPort("mh18", "x", PortDirection::Out, nullptr, "logic");
    checkPort("mh18", "y", PortDirection::In, wire, "logic");
    checkPort("mh19", "x", PortDirection::Out, wire, "logic signed[5:0]");
    checkPort("mh19", "y", PortDirection::Out, nullptr, "integer");
    checkPort("mh20", "x", PortDirection::Ref, nullptr, "logic[5:0]");
    checkPort("mh20", "y", PortDirection::Ref, nullptr, "logic[5:0]");
    checkPort("mh21", "x", PortDirection::Ref, nullptr, "logic$[5:0]");
    checkPort("mh21", "y", PortDirection::Ref, nullptr, "logic");

    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InOutPortCannotBeVariable);
    CHECK(diags[1].code == diag::RefPortMustBeVariable);
}

#ifdef _MSC_VER
#    pragma warning(disable : 4127)
#endif

TEST_CASE("Module ANSI interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I; modport bar(input f); endinterface
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
    auto& diags = compilation.getAllDiagnostics();

#define checkIfacePort(moduleName, portName, ifaceName, modportName)            \
    {                                                                           \
        auto def = compilation.getDefinition(moduleName);                       \
        REQUIRE(def);                                                           \
        auto& port = def->getPortMap().at(portName)->as<InterfacePortSymbol>(); \
        REQUIRE(port.interfaceDef);                                             \
        CHECK(port.interfaceDef->name == (ifaceName));                          \
        if (*(modportName)) {                                                   \
            REQUIRE(port.modport);                                              \
            CHECK(port.modport->name == (modportName));                         \
        }                                                                       \
        else {                                                                  \
            CHECK(!port.modport);                                               \
        }                                                                       \
    };

    auto wire = &compilation.getWireNetType();

    checkIfacePort("m0", "a", "I", "");
    checkIfacePort("m0", "b", "I", "");
    checkPort("m0", "c", PortDirection::In, wire, "logic");
    checkPort("m1", "j", PortDirection::InOut, wire, "struct{logic f;}J");
    checkIfacePort("m3", "k", "K", "");
    checkPort("m3", "w", PortDirection::InOut, wire, "logic");
    checkPort("m4", "v", PortDirection::Out, nullptr, "logic");
    checkIfacePort("m5", "a1", "J", "");
    checkIfacePort("m5", "a2", "K", "");
    checkIfacePort("m6", "bar", "I", "bar");

    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::PortTypeNotInterfaceOrData);
    CHECK(diags[1].code == diag::VarWithInterfacePort);
    CHECK(diags[2].code == diag::DirectionWithInterfacePort);
    CHECK(diags[3].code == diag::UnknownMember);
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

    checkPort("test", "a", PortDirection::InOut, wire, "logic");
    checkPort("test", "b", PortDirection::Ref, wire, "logic");
    checkPort("test", "c", PortDirection::Ref, nullptr, "logic");
    checkPort("test", "d", PortDirection::InOut, nullptr, "logic");
    checkPort("test", "e", PortDirection::In, wire, "logic");
    checkPort("test", "f", PortDirection::Ref, wire, "logic");

    checkPort("test", "g", PortDirection::In, nullptr, "logic");
    checkPort("test", "h", PortDirection::In, nullptr, "struct{logic f;}test.s$2");
    checkPort("test", "i", PortDirection::Out, wire, "logic[2:0]");
    checkPort("test", "j", PortDirection::Out, wire, "logic");
    checkPort("test", "k", PortDirection::In, nullptr, "struct{logic f;}test.s$1");
    checkPort("test", "l", PortDirection::In, nullptr, "logic[1:0]$[0:1]");
    checkPort("test", "m", PortDirection::In, nullptr, "logic[2:0]");
    checkPort("test", "n", PortDirection::In, nullptr, "logic$[0:2]");
    checkPort("test", "o", PortDirection::In, nullptr, "logic[2:0]$[0:2]");
    checkPort("test", "p", PortDirection::In, nullptr, "logic[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "q", PortDirection::In, nullptr, "logic signed[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "r", PortDirection::In, nullptr, "logic signed[2:0][3:2]$[1:2][2:0][0:4]");

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

    checkPort("test", "a", PortDirection::In, wire, "logic[7:0]");
    checkPort("test", "b", PortDirection::In, wire, "logic signed[7:0]");
    checkPort("test", "c", PortDirection::In, wire, "logic signed[7:0]");
    checkPort("test", "d", PortDirection::In, wire, "logic signed[7:0]");
    checkPort("test", "e", PortDirection::Out, wire, "logic[7:0]");
    checkPort("test", "f", PortDirection::Out, nullptr, "logic signed[7:0]");
    checkPort("test", "g", PortDirection::Out, nullptr, "logic signed[7:0]");
    checkPort("test", "h", PortDirection::Out, wire, "logic signed[7:0]");

    NO_COMPILATION_ERRORS;
}


TEST_CASE("Simple port connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input int a, b, c);
endmodule

module test;
    logic foo;
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
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::MixingOrderedAndNamedPorts);
    CHECK((it++)->code == diag::DuplicateWildcardPortConnection);
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

module test;

    logic a[5];
    m m1(.a(a));
    
    logic b[3][4][5];
    m m2 [3][4] (.a(b));

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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
    CHECK(diags[0].code == diag::DefinitionUsedAsType);
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