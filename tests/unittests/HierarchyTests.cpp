#include "Test.h"

TEST_CASE("Finding top level") {
    auto file1 = SyntaxTree::fromText(
        "module A; endmodule\nmodule B; A a(); endmodule\nmodule C; endmodule");
    auto file2 = SyntaxTree::fromText(
        "module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    Compilation compilation;
    compilation.addSyntaxTree(file1);
    compilation.addSyntaxTree(file2);

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
    CHECK(root.topInstances[0]->name == "C");
    CHECK(root.topInstances[1]->name == "D");
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Finding top level - 2") {
    auto tree1 = SyntaxTree::fromText(R"(
module top;
endmodule

module nottop;
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
module foo #(parameter int f = 2) ();
    if (f != 2) begin
        nottop nt();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
    CHECK(root.topInstances[0]->name == "foo");
    CHECK(root.topInstances[1]->name == "top");
}

TEST_CASE("Top level params") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int foo = 3) ();
endmodule

module NotTop #(parameter int foo) ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->name == "Top");
}

TEST_CASE("Module parameterization errors") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    Leaf l1();
    Leaf #(1, 2, 3, 4) l2();
    Leaf #(1, 2, 3, 4, 5) l3();
    Leaf #(.foo(3), .baz(9)) l4();
    Leaf #(.unset(10), .bla(7)) l5();
    Leaf #(.unset(10), .localp(7)) l6();
    Leaf #(.unset(10), .unset(7)) l7();
    Leaf #(.unset(10), 5) l8();
    Leaf #(.unset(10)) l9(); // no errors on this one
endmodule

module Leaf #(
    int foo = 4,
    int bar = 9,
    localparam int baz,
    parameter bizz = baz,
    parameter int unset
    )();

    parameter int localp;

endmodule
)");

    Compilation compilation;
    auto it = evalModule(tree, compilation).membersOfType<ModuleInstanceSymbol>().begin();
    CHECK(it->name == "l1");
    it++;
    CHECK(it->name == "l2");
    it++;
    CHECK(it->name == "l3");
    it++;
    CHECK(it->name == "l4");
    it++;
    CHECK(it->name == "l5");
    it++;
    CHECK(it->name == "l6");
    it++;
    CHECK(it->name == "l7");
    it++;
    CHECK(it->name == "l8");
    it++;
    CHECK(it->name == "l9");
    it++;

    auto& diags = compilation.getSemanticDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::ParamHasNoValue);
    CHECK(diags[1].code == diag::TooManyParamAssignments);
    CHECK(diags[2].code == diag::ParamHasNoValue);
    CHECK(diags[3].code == diag::AssignedToLocalPortParam);
    CHECK(diags[4].code == diag::ParameterDoesNotExist);
    CHECK(diags[5].code == diag::AssignedToLocalBodyParam);
    CHECK(diags[6].code == diag::DuplicateParamAssignment);
    CHECK(diags[7].code == diag::MixingOrderedAndNamedParams);
    CHECK(diags[8].code == diag::LocalParamNoInitializer);
    CHECK(diags[9].code == diag::BodyParamNoInitializer);

    REQUIRE(diags[3].notes.size() == 1);
    REQUIRE(diags[5].notes.size() == 1);
    REQUIRE(diags[6].notes.size() == 1);
    CHECK(diags[3].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[5].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[6].notes[0].code == diag::NotePreviousUsage);
}

TEST_CASE("Module children (simple)") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    Child child();
endmodule

module Child;
    Leaf leaf();
endmodule

module Leaf #(parameter int foo = 4)();
    parameter localp = foo;
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& leaf = instance.memberAt<ModuleInstanceSymbol>(0).memberAt<ModuleInstanceSymbol>(0);
    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (conditional generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    Child child();
endmodule

module Child #(parameter foo = 4)();
    if (foo == 4) begin
        Leaf #(1) leaf();
    end
    else begin
        if (1) always_comb blaz = blob;
        Leaf #(2) leaf();
    end
endmodule

module Leaf #(parameter int foo = 4)();
    parameter localp = foo;
endmodule
)");

    Compilation compilation;
    auto& instance = evalModule(tree, compilation);
    auto& child = instance.memberAt<ModuleInstanceSymbol>(0);
    CHECK(child.memberAt<GenerateBlockSymbol>(1).isInstantiated);
    CHECK(!child.memberAt<GenerateBlockSymbol>(2).isInstantiated);

    auto& leaf = child.memberAt<GenerateBlockSymbol>(1).memberAt<ModuleInstanceSymbol>(0);
    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (loop generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int limit = 10)();
    for (genvar i = 0; i < limit; i += 1) begin
        Leaf #(i) leaf();
    end
endmodule

module Leaf #(parameter int foo)();
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).memberAt<GenerateBlockArraySymbol>(1);

    REQUIRE(instance.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        const auto& leaf =
            instance.memberAt<GenerateBlockSymbol>(i).memberAt<ModuleInstanceSymbol>(1);
        const auto& foo = leaf.find<ParameterSymbol>("foo");
        CHECK(foo.getValue().integer() == i);
    }
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (case generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int val = 10)();
    case (val)
        2,3: begin : u1 end
        10: u2: begin end
    endcase
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    compilation.getRoot().lookupName<GenerateBlockSymbol>("Top.u2");
}

TEST_CASE("Interface instantiation") {
    auto tree = SyntaxTree::fromText(R"(
interface I2CBus(
    input wire clk,
    input wire rst);

    logic scl_i;
    logic sda_i;
    logic scl_o;
    logic sda_o;

    modport master (input clk, rst, scl_i, sda_i,
                    output scl_o, sda_o);

endinterface

module Top;
    logic clk;
    logic rst;

    I2CBus bus(.*);
endmodule
)");

    Compilation compilation;
    evalModule(tree, compilation);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("always_comb") {
    auto tree = SyntaxTree::fromText(R"(
module module1
#(
    parameter int P1 = 4,
    parameter int P2 = 5
)
(
    input  logic [P1-1:0]   in1,
    input  logic [P2-1:0]   in2,
    input  logic [3:0]      in3,

    output logic [P1-1:0]   out1,
    output logic [P1-1:0]   out2,
    output logic [P1-1:0]   out3
);

    always_comb out1 = in1;

    always_comb begin
        out2 = in2;
        out3 = in3;
    end

    logic [7:0] arr1;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& alwaysComb = instance.memberAt<ProceduralBlockSymbol>(14);

    CHECK(alwaysComb.procedureKind == ProceduralBlockKind::AlwaysComb);

    const auto& variable = instance.memberAt<VariableSymbol>(16);
    CHECK(variable.getType().isIntegral());
    CHECK(variable.name == "arr1");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Function declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    function static logic [15:0] foo(a, int b, output logic [15:0] u, v, inout w);
        return a + b;
    endfunction
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& foo = instance.memberAt<SubroutineSymbol>(0);
    CHECK(foo.subroutineKind == SubroutineKind::Function);
    CHECK(foo.defaultLifetime == VariableLifetime::Static);
    CHECK(foo.getReturnType().getBitWidth() == 16);
    CHECK(foo.name == "foo");

    auto args = foo.arguments;
    REQUIRE(args.size() == 5);
    CHECK(args[0]->getType().getBitWidth() == 1);
    CHECK(args[0]->direction == FormalArgumentDirection::In);
    CHECK(args[1]->getType().getBitWidth() == 32);
    CHECK(args[1]->direction == FormalArgumentDirection::In);
    CHECK(args[2]->getType().getBitWidth() == 16);
    CHECK(args[2]->direction == FormalArgumentDirection::Out);
    CHECK(args[3]->getType().getBitWidth() == 16);
    CHECK(args[3]->direction == FormalArgumentDirection::Out);
    CHECK(args[4]->getType().getBitWidth() == 1);
    CHECK(args[4]->direction == FormalArgumentDirection::InOut);

    const auto& returnStmt = foo.getBody().as<ReturnStatement>();
    REQUIRE(returnStmt.kind == StatementKind::Return);
    CHECK(!returnStmt.expr->bad());
    CHECK(returnStmt.expr->type->getBitWidth() == 16);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    parameter int blah = Foo::x;
endmodule

package Foo;
    parameter int x = 4;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    auto& cv = compilation.getRoot().topInstances[0]->memberAt<ParameterSymbol>(0).getValue();
    CHECK(cv.integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive parameter / function") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam logic [bar()-1:0] foo = 1;

    function logic[$bits(foo)-1:0] bar;
        return 1;
    endfunction

    localparam int baz = fun();
    localparam int bax = baz;

    function logic[bax-1:0] fun;
        return 1;
    endfunction

    localparam int a = stuff();
    localparam int b = a;

    function int stuff;
        return b;
    endfunction

    localparam int z = stuff2();
    logic [3:0] y;

    function int stuff2;
        return $bits(y);
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::RecursiveDefinition);
    CHECK(diags[1].code == diag::RecursiveDefinition);
    CHECK(diags[2].code == diag::ExpressionNotConstant);
    CHECK(diags[3].code == diag::RecursiveDefinition);
    CHECK(diags[4].code == diag::ExpressionNotConstant);
}

TEST_CASE("Parameter ordering from const func") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam int a = 1;

    if (1) begin
        if (1) begin
            function int stuff;
                return a;
            endfunction

            localparam int b = stuff;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface param from const func") {
    auto tree1 = SyntaxTree::fromText(R"(
interface I #(parameter int foo = 1);
endinterface
)");
    auto tree2 = SyntaxTree::fromText(R"(
module M(I i);
    if (1) begin
        if (1) begin
            function int stuff;
                return i.foo;
            endfunction

            localparam int b = stuff;
        end
    end
endmodule

module top;
    I i();
    M m(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;
}

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
        if (*(modportName)) {                                                     \
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
    checkPort("test", "h", PortDirection::In, nullptr, "struct{logic f;}");
    checkPort("test", "i", PortDirection::Out, wire, "logic[2:0]");
    checkPort("test", "j", PortDirection::Out, wire, "logic");
    checkPort("test", "k", PortDirection::In, nullptr, "struct{logic f;}");
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
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::MixingOrderedAndNamedPorts);
    CHECK((it++)->code == diag::DuplicateWildcardPortConnection);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::UnconnectedNamedPort);
    CHECK((it++)->code == diag::DuplicatePortConnection);
    CHECK((it++)->code == diag::InterfacePortNotConnected);
    CHECK((it++)->code == diag::InterfacePortInvalidExpression);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::NotAnInterface);
    CHECK((it++)->code == diag::InterfacePortTypeMismatch);
    CHECK((it++)->code == diag::PortConnDimensionsMismatch);
    CHECK(it == diags.end());

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("test.q1.p1[1].bar");
    CHECK(bar.getValue().integer() == 42);
}

TEST_CASE("Interface port param") {
    auto tree = SyntaxTree::fromText(R"(

interface I #(parameter int i) ();
endinterface

module M(I iface, logic [iface.i - 1 : 0] foo);
    localparam int j = $bits(foo);
endmodule

module test;

    I #(17) i();
    M m(i, 1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto top = compilation.getRoot().topInstances[0];
    auto& j = top->find<ModuleInstanceSymbol>("m").find<ParameterSymbol>("j");
    CHECK(j.getValue().integer() == 17);
}

TEST_CASE("Generate dependent on iface port param") {
    auto tree = SyntaxTree::fromText(R"(

interface I #(parameter int i) ();
endinterface

module N;
endmodule

module M(I iface, logic [iface.i - 1 : 0] foo);
    localparam int j = $bits(foo);
    if (j == 17) begin : asdf
        N n();
    end
endmodule

module test;

    I #(17) i();
    M m(i, 1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& asdf = compilation.getRoot().lookupName<GenerateBlockSymbol>("test.m.asdf");
    CHECK(asdf.isInstantiated);
}

TEST_CASE("Name conflict bug") {
    auto tree = SyntaxTree::fromText(R"(
module m(logic stuff);
    logic foo;
    logic[$bits(stuff)-1:0] foo;
endmodule

module n;
    m m1(.stuff(1));
endmodule
)");

    // This just tests that we don't crash.
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}

TEST_CASE("Loop generate errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    if (1) begin : blah
        int foo;
    end

    genvar i, j;
    localparam int l = 0;
    struct { logic l; } us;
    logic arr[2];

    for (i = i; i + 1; i + 1) begin end         // iter expr doesn't change genvar
    for (i = 0; i; --i) begin end               // not an error
    for (i = 0; i; i++) begin end               // not an error
    for ( = 0; i; i++) begin end                // missing genvar
    for (i = 0; i; j++) begin end               // different name in init and incr
    for (k = 0; k; k++) begin end               // missing genvar
    for (l = 0; l; l++) begin end               // l is not a genvar
    for (i = 0; i < blah.foo; i++) begin end    // non-constant stop expr
    for (i = 0; i; i += blah.foo) begin end     // non-constant iter expr
    for (i = 0; us; i++) begin end              // stop expr is not boolean
    for (i = 'x; i; i++) begin end              // unknown in init
    for (i = 0; i < 10; i += 'x) begin end      // unknown in iter
    for (i = 0; i < 10; i += 0) begin end       // repeated val
    for (i = 0; i < 10; i += arr[i+4]) name: begin end       // bad iter expr

    for (i = 0; i; --i) foo: begin : baz end    // name and label

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::NotAValue);
    CHECK((it++)->code == diag::InvalidGenvarIterExpression);
    CHECK((it++)->code == diag::ExpectedIdentifier);
    CHECK((it++)->code == diag::ExpectedGenvarIterVar);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::NotAGenvar);
    CHECK((it++)->code == diag::HierarchicalNotAllowedInConstant);
    CHECK((it++)->code == diag::HierarchicalNotAllowedInConstant);
    CHECK((it++)->code == diag::NotBooleanConvertible);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarDuplicate);
    CHECK((it++)->code == diag::ExpressionNotConstant);
    CHECK((it++)->code == diag::LabelAndName);
    CHECK(it == diags.end());
}

TEST_CASE("Case generate corner cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    case (i) endcase
    case (j) 0: begin end endcase

    case (1)
        1: begin end
        1: begin end
    endcase

    case (1)
        0: begin end
    endcase

    case (1)
        default: begin end
        default: begin end
    endcase

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::CaseGenerateEmpty);
    CHECK((it++)->code == diag::ExpressionNotConstant);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::CaseGenerateDup);
    CHECK((it++)->code == diag::CaseGenerateNoBlock);
    CHECK((it++)->code == diag::MultipleGenerateDefaultCases);
    CHECK(it == diags.end());
}

TEST_CASE("Conditional generate same name") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    localparam p = 2, q = 1;

    if (p == 1)
        if (q == 0) begin : u1 localparam int foo = 1; end
        else if (q == 2) begin : u1 localparam int foo = 2; end
        else ;
    else if (p == 2)
        case (q)
            0, 1, 2: begin : u1 localparam int foo = 3; end
            default: begin : u1 localparam int foo = 4; end
        endcase

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.u1.foo");
    CHECK(foo.getValue().integer() == 3);
}

TEST_CASE("Cross-CU definition lookup") {
    auto tree1 = SyntaxTree::fromText(R"(
module m #(parameter int count = 0);

    Iface ifaces[count] ();
    Blah blah(.ifaces(ifaces));

endmodule

module Blah(Iface ifaces[3]);
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
interface Iface;
endinterface
)");
    auto tree3 = SyntaxTree::fromText(R"(
module top;
    m #(3) inst ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Cross-CU package import") {
    auto tree1 = SyntaxTree::fromText(R"(
module m import pkg::*; #(parameter foo_t count = 0);
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
package pkg;
    typedef int foo_t;
endpackage
)");
    auto tree3 = SyntaxTree::fromText(R"(
module top;
    m #(3) inst ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module/instance paths in errors") {
    auto tree = SyntaxTree::fromText(R"(
module foo;
    if (1) begin : gen
        bar b();
    end
endmodule

module bar;
    baz #(1) z1();
    baz #(2) z2();
    baz #(3) z3();
endmodule

module baz #(parameter int i)();
    if (i == 1 || i == 3) begin
        always asdf = 1;
    end
endmodule
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
  in 2 instances, e.g. foo.gen.b.z3
source:16:16: error: use of undeclared identifier 'asdf'
        always asdf = 1;
               ^~~~
)");
}

TEST_CASE("Interface array port selection") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
endinterface

module m (Iface i);
endmodule

module n (Iface arr[4]);
    for (genvar i = 0; i < 4; i++) begin
        m minst(.i(arr[i]));
    end
endmodule

module top;
    Iface arr[4] (.*);
    n ninst(.arr);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter with type imported from package") {
    auto tree1 = SyntaxTree::fromText(R"(
module m #(parameter p::foo f = "SDF") ();
    if (f == "BAR") begin: block1
        l #(.f(f)) l1();
    end
    else begin: block2
        l #(.f(f)) l1();
    end 
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
package p;
    typedef string foo;
endpackage
)");
    auto tree3 = SyntaxTree::fromText(R"(
module l #(p::foo f) ();
endmodule
)");
    auto tree4 = SyntaxTree::fromText(R"(
module top;
    m m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree4);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Local interface not considered hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic [3:0] foo;
endinterface

module m;
    I i();
    localparam int j = $bits(i.foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& j = compilation.getRoot().lookupName<ParameterSymbol>("m.j");
    CHECK(j.getValue().integer() == 4);
}

TEST_CASE("Local interface declared later considered hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic [3:0] foo;
endinterface

module m;
    localparam int j = $bits(i.foo);
    I i();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
}

TEST_CASE("Recursive modules -- if generate") {
    auto tree = SyntaxTree::fromText(R"(
module bar #(parameter int c) ();
    if (c == 99) bar #(99) b();
endmodule

module foo #(parameter int count = 2) ();
    if (count == 2) begin end
    else begin
        bar #(99) asdf();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive modules -- invalid") {
    auto tree = SyntaxTree::fromText(R"(
module bar;
    foo f();
endmodule

module foo #(parameter int count = 2) ();
    foo #(count * 2 + 1) f();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MaxInstanceDepthExceeded);
}