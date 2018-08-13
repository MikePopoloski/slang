#include "Test.h"

TEST_CASE("Finding top level", "[binding:decls]") {
    auto file1 = SyntaxTree::fromText("module A; A a(); endmodule\nmodule B; endmodule\nmodule C; endmodule");
    auto file2 = SyntaxTree::fromText("module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    Compilation compilation;
    compilation.addSyntaxTree(file1);
    compilation.addSyntaxTree(file2);

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
    CHECK(root.topInstances[0]->name == "C");
    CHECK(root.topInstances[1]->name == "D");
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module parameterization errors", "[binding:modules]") {
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

// TODO: handle implicit types here?
module Leaf #(
    int foo = 4,
    int bar = 9,
    localparam int baz,
    parameter int bizz = baz,
    parameter int unset
    )();

    parameter int localp;

endmodule
)");

    Compilation compilation;
    auto it = evalModule(tree, compilation).membersOfType<ModuleInstanceSymbol>().begin();
    CHECK(it->name == "l1"); it++;
    CHECK(it->name == "l2"); it++;
    CHECK(it->name == "l3"); it++;
    CHECK(it->name == "l4"); it++;
    CHECK(it->name == "l5"); it++;
    CHECK(it->name == "l6"); it++;
    CHECK(it->name == "l7"); it++;
    CHECK(it->name == "l8"); it++;
    CHECK(it->name == "l9"); it++;

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

TEST_CASE("Module children (simple)", "[binding:modules]") {
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

TEST_CASE("Module children (conditional generate)", "[binding:modules]") {
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
    const auto& leaf = instance
        .memberAt<ModuleInstanceSymbol>(0)
        .memberAt<GenerateBlockSymbol>(1)
        .memberAt<ModuleInstanceSymbol>(0);

    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (loop generate)", "[binding:modules]") {
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

    // TODO: size of the range?
    //REQUIRE(instance.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        const auto& leaf = instance.memberAt<GenerateBlockSymbol>(i).memberAt<ModuleInstanceSymbol>(1);
        const auto& foo = leaf.find<ParameterSymbol>("foo");
        CHECK(foo.getValue().integer() == i);
    }
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface instantiation", "[binding:modules]") {
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

TEST_CASE("always_comb", "[binding:modules]") {
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
    const auto& alwaysComb = instance.memberAt<ProceduralBlockSymbol>(8);

    CHECK(alwaysComb.procedureKind == ProceduralBlockKind::AlwaysComb);

    const auto& variable = instance.memberAt<VariableSymbol>(10);
    CHECK(variable.getType().isIntegral());
    CHECK(variable.name == "arr1");

    // TODO:
    //NO_COMPILATION_ERRORS;
}

TEST_CASE("Function declaration", "[binding:modules]") {
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

TEST_CASE("Package declaration", "[symbols]") {
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
    //REQUIRE(diags.size() == 5);
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::RecursiveDefinition);
    CHECK(diags[1].code == DiagCode::RecursiveDefinition);
    CHECK(diags[2].code == DiagCode::ExpressionNotConstant);
    CHECK(diags[3].code == DiagCode::RecursiveDefinition);
    //CHECK(diags[4].code == DiagCode::ExpressionNotConstant);
}