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

    Diagnostics diags = compilation.getSemanticDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == DiagCode::ParamHasNoValue);
    CHECK(diags[1].code == DiagCode::TooManyParamAssignments);
    CHECK(diags[2].code == DiagCode::ParamHasNoValue);
    CHECK(diags[3].code == DiagCode::AssignedToLocalPortParam);
    CHECK(diags[4].code == DiagCode::ParameterDoesNotExist);
    CHECK(diags[5].code == DiagCode::AssignedToLocalBodyParam);
    CHECK(diags[6].code == DiagCode::DuplicateParamAssignment);
    CHECK(diags[7].code == DiagCode::MixingOrderedAndNamedParams);
    CHECK(diags[8].code == DiagCode::LocalParamNoInitializer);
    CHECK(diags[9].code == DiagCode::BodyParamNoInitializer);

    REQUIRE(diags[3].notes.size() == 1);
    REQUIRE(diags[5].notes.size() == 1);
    REQUIRE(diags[6].notes.size() == 1);
    CHECK(diags[3].notes[0].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[5].notes[0].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[6].notes[0].code == DiagCode::NotePreviousUsage);
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
        Leaf #(2) leaf();
    end
endmodule

module Leaf #(parameter int foo = 4)();
    parameter localp = foo;
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& leaf = instance.memberAt<ModuleInstanceSymbol>(0)
                           .memberAt<GenerateBlockSymbol>(1)
                           .memberAt<ModuleInstanceSymbol>(0);

    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (loop generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    for (genvar i = 0; i < 10; i += 1) begin
        Leaf #(i) leaf();
    end
endmodule

module Leaf #(parameter int foo)();
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).memberAt<GenerateBlockArraySymbol>(0);

    REQUIRE(instance.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        const auto& leaf =
            instance.memberAt<GenerateBlockSymbol>(i).memberAt<ModuleInstanceSymbol>(1);
        const auto& foo = leaf.find<ParameterSymbol>("foo");
        CHECK(foo.getValue().integer() == i);
    }
    NO_COMPILATION_ERRORS;
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

    // TODO:
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
    CHECK(!foo.isTask);
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

    const auto& returnStmt = foo.getBody()->as<StatementList>().list[0]->as<ReturnStatement>();
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

    Diagnostics diags = compilation.getAllDiagnostics();
    // TODO: $bits() function should check argument even though it's not evaluated
    // REQUIRE(diags.size() == 5);
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::RecursiveDefinition);
    CHECK(diags[1].code == DiagCode::RecursiveDefinition);
    CHECK(diags[2].code == DiagCode::ExpressionNotConstant);
    CHECK(diags[3].code == DiagCode::RecursiveDefinition);
    // CHECK(diags[4].code == DiagCode::ExpressionNotConstant);
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
    Diagnostics diags = compilation.getAllDiagnostics();

#define checkPort(moduleName, name, dir, kind, type)               \
    {                                                              \
        auto def = compilation.getDefinition(moduleName);          \
        REQUIRE(def);                                              \
        auto& port = def->getPortMap().at(name)->as<PortSymbol>(); \
        CHECK(port.direction == (dir));                            \
        CHECK(port.portKind == (kind));                            \
        CHECK(port.getType().toString() == (type));                \
    };

    checkPort("mh0", "x", PortDirection::InOut, PortKind::Net, "logic");
    checkPort("mh1", "x", PortDirection::InOut, PortKind::Net, "integer");
    checkPort("mh2", "x", PortDirection::InOut, PortKind::Net, "integer");
    checkPort("mh3", "x", PortDirection::InOut, PortKind::Net, "logic[5:0]");
    checkPort("mh4", "x", PortDirection::InOut, PortKind::Variable, "logic");
    checkPort("mh5", "x", PortDirection::In, PortKind::Net, "logic");
    checkPort("mh6", "x", PortDirection::In, PortKind::Variable, "logic");
    checkPort("mh7", "x", PortDirection::In, PortKind::Variable, "integer");
    checkPort("mh8", "x", PortDirection::Out, PortKind::Net, "logic");
    checkPort("mh9", "x", PortDirection::Out, PortKind::Variable, "logic");
    checkPort("mh10", "x", PortDirection::Out, PortKind::Net, "logic signed[5:0]");
    checkPort("mh11", "x", PortDirection::Out, PortKind::Variable, "integer");
    checkPort("mh12", "x", PortDirection::Ref, PortKind::Variable, "logic[5:0]");
    checkPort("mh13", "x", PortDirection::Ref, PortKind::Variable, "logic$[5:0]");
    checkPort("mh14", "x", PortDirection::InOut, PortKind::Net, "logic");
    checkPort("mh14", "y", PortDirection::InOut, PortKind::Net, "logic$[7:0]");
    checkPort("mh15", "x", PortDirection::InOut, PortKind::Net, "integer");
    checkPort("mh15", "y", PortDirection::InOut, PortKind::Net, "logic signed[5:0]");
    checkPort("mh16", "x", PortDirection::InOut, PortKind::Net, "logic[5:0]");
    checkPort("mh16", "y", PortDirection::InOut, PortKind::Net, "logic");
    checkPort("mh17", "x", PortDirection::In, PortKind::Variable, "integer");
    checkPort("mh17", "y", PortDirection::In, PortKind::Net, "logic");
    checkPort("mh18", "x", PortDirection::Out, PortKind::Variable, "logic");
    checkPort("mh18", "y", PortDirection::In, PortKind::Net, "logic");
    checkPort("mh19", "x", PortDirection::Out, PortKind::Net, "logic signed[5:0]");
    checkPort("mh19", "y", PortDirection::Out, PortKind::Variable, "integer");
    checkPort("mh20", "x", PortDirection::Ref, PortKind::Variable, "logic[5:0]");
    checkPort("mh20", "y", PortDirection::Ref, PortKind::Variable, "logic[5:0]");
    checkPort("mh21", "x", PortDirection::Ref, PortKind::Variable, "logic$[5:0]");
    checkPort("mh21", "y", PortDirection::Ref, PortKind::Variable, "logic");

    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == DiagCode::InOutPortCannotBeVariable);
    CHECK(diags[1].code == DiagCode::RefPortMustBeVariable);
}

#ifdef _MSC_VER
#    pragma warning(disable : 4127)
#endif

TEST_CASE("Module ANSI interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I; modport bar(); endinterface
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
    Diagnostics diags = compilation.getAllDiagnostics();

#define checkIfacePort(moduleName, portName, ifaceName, modportName)            \
    {                                                                           \
        auto def = compilation.getDefinition(moduleName);                       \
        REQUIRE(def);                                                           \
        auto& port = def->getPortMap().at(portName)->as<InterfacePortSymbol>(); \
        REQUIRE(port.interfaceDef);                                             \
        CHECK(port.interfaceDef->name == (ifaceName));                          \
        if (modportName) {                                                      \
            REQUIRE(port.modport);                                              \
            CHECK(port.modport->name == (modportName));                         \
        }                                                                       \
        else {                                                                  \
            CHECK(!port.modport);                                               \
        }                                                                       \
    };

    checkIfacePort("m0", "a", "I", nullptr);
    checkIfacePort("m0", "b", "I", nullptr);
    checkPort("m0", "c", PortDirection::In, PortKind::Net, "logic");
    checkPort("m1", "j", PortDirection::InOut, PortKind::Net, "struct{logic f;}J");
    checkIfacePort("m3", "k", "K", nullptr);
    checkPort("m3", "w", PortDirection::InOut, PortKind::Net, "logic");
    checkPort("m4", "v", PortDirection::Out, PortKind::Variable, "logic");
    checkIfacePort("m5", "a1", "J", nullptr);
    checkIfacePort("m5", "a2", "K", nullptr);
    checkIfacePort("m6", "bar", "I", "bar");

    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == DiagCode::PortTypeNotInterfaceOrData);
    CHECK(diags[1].code == DiagCode::VarWithInterfacePort);
    CHECK(diags[2].code == DiagCode::DirectionWithInterfacePort);
    CHECK(diags[3].code == DiagCode::UnknownMember);
    CHECK(diags[4].code == DiagCode::NotAModport);
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

    checkPort("test", "a", PortDirection::InOut, PortKind::Net, "logic");
    checkPort("test", "b", PortDirection::Ref, PortKind::Net, "logic");
    checkPort("test", "c", PortDirection::Ref, PortKind::Variable, "logic");
    checkPort("test", "d", PortDirection::InOut, PortKind::Variable, "logic");
    checkPort("test", "e", PortDirection::In, PortKind::Net, "logic");
    checkPort("test", "f", PortDirection::Ref, PortKind::Net, "logic");

    checkPort("test", "g", PortDirection::In, PortKind::Variable, "logic");
    checkPort("test", "h", PortDirection::In, PortKind::Variable, "struct{logic f;}");
    checkPort("test", "i", PortDirection::Out, PortKind::Net, "logic[2:0]");
    checkPort("test", "j", PortDirection::Out, PortKind::Net, "logic");
    checkPort("test", "k", PortDirection::In, PortKind::Variable, "struct{logic f;}");
    checkPort("test", "l", PortDirection::In, PortKind::Variable, "logic[1:0]$[0:1]");
    checkPort("test", "m", PortDirection::In, PortKind::Variable, "logic[2:0]");
    checkPort("test", "n", PortDirection::In, PortKind::Variable, "logic$[0:2]");
    checkPort("test", "o", PortDirection::In, PortKind::Variable, "logic[2:0]$[0:2]");
    checkPort("test", "p", PortDirection::In, PortKind::Variable,
              "logic[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "q", PortDirection::In, PortKind::Variable,
              "logic signed[2:0][3:1]$[1:2][2:0][0:4]");
    checkPort("test", "r", PortDirection::In, PortKind::Variable,
              "logic signed[2:0][3:2]$[1:2][2:0][0:4]");

    Diagnostics diags = compilation.getAllDiagnostics();

    auto it = diags.begin();
    CHECK((it++)->code == DiagCode::Redefinition);
    CHECK((it++)->code == DiagCode::Redefinition);
    CHECK((it++)->code == DiagCode::RefPortMustBeVariable);
    CHECK((it++)->code == DiagCode::InOutPortCannotBeVariable);
    CHECK((it++)->code == DiagCode::RefPortMustBeVariable);
    CHECK((it++)->code == DiagCode::Redefinition);
    CHECK((it++)->code == DiagCode::RedefinitionDifferentType);
    CHECK((it++)->code == DiagCode::CantDeclarePortSigned);
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

    checkPort("test", "a", PortDirection::In, PortKind::Net, "logic[7:0]");
    checkPort("test", "b", PortDirection::In, PortKind::Net, "logic signed[7:0]");
    checkPort("test", "c", PortDirection::In, PortKind::Net, "logic signed[7:0]");
    checkPort("test", "d", PortDirection::In, PortKind::Net, "logic signed[7:0]");
    checkPort("test", "e", PortDirection::Out, PortKind::Net, "logic[7:0]");
    checkPort("test", "f", PortDirection::Out, PortKind::Variable, "logic signed[7:0]");
    checkPort("test", "g", PortDirection::Out, PortKind::Variable, "logic signed[7:0]");
    checkPort("test", "h", PortDirection::Out, PortKind::Net, "logic signed[7:0]");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module port connections") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a, b, c);
endmodule

module test;

    m m1(1, 1, 1);
    //m m2(1, , 1);
    m m3(1, 0);             // warning about unconnected
    m m4(1, .b());          // error: mixing
    m m5(.*, .a, .*);       // error: duplicate wildcard
    m m6(.a(), .b);         // warning about unconnected
    m m7(.a, .a());         // error: duplicate
    m m8(.a(1+0), .b, .c);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    Diagnostics diags = compilation.getAllDiagnostics();

    auto it = diags.begin();
    CHECK((it++)->code == DiagCode::MixingOrderedAndNamedPorts);
    CHECK((it++)->code == DiagCode::DuplicateWildcardPortConnection);
    CHECK((it++)->code == DiagCode::DuplicatePortConnection);
    CHECK(it == diags.end());
}