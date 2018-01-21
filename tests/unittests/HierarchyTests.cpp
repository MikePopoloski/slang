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
    evalModule(tree, compilation).members();

    const auto& diags = compilation.getSemanticDiagnostics();
    REQUIRE(diags.size() == 13);
    CHECK(diags[0].code == DiagCode::LocalParamNoInitializer);
    CHECK(diags[1].code == DiagCode::BodyParamNoInitializer);
    CHECK(diags[2].code == DiagCode::ParamHasNoValue);
    CHECK(diags[3].code == DiagCode::TooManyParamAssignments);
    CHECK(diags[4].code == DiagCode::AssignedToLocalPortParam);
    CHECK(diags[5].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[6].code == DiagCode::ParamHasNoValue);
    CHECK(diags[7].code == DiagCode::ParameterDoesNotExist);
    CHECK(diags[8].code == DiagCode::AssignedToLocalBodyParam);
    CHECK(diags[9].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[10].code == DiagCode::DuplicateParamAssignment);
    CHECK(diags[11].code == DiagCode::NotePreviousUsage);
    CHECK(diags[12].code == DiagCode::MixingOrderedAndNamedParams);
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
    const auto& alwaysComb = instance.memberAt<ProceduralBlockSymbol>(2);

    CHECK(alwaysComb.procedureKind == ProceduralBlockKind::AlwaysComb);

    const auto& variable = instance.memberAt<VariableSymbol>(4);
    CHECK(variable.type->isIntegral());
    CHECK(variable.name == "arr1");

    NO_COMPILATION_ERRORS;
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
    CHECK(foo.returnType->getBitWidth() == 16);
    CHECK(foo.name == "foo");

    auto args = foo.arguments;
    REQUIRE(args.size() == 5);
    CHECK(args[0]->type->getBitWidth() == 1);
    CHECK(args[0]->direction == FormalArgumentDirection::In);
    CHECK(args[1]->type->getBitWidth() == 32);
    CHECK(args[1]->direction == FormalArgumentDirection::In);
    CHECK(args[2]->type->getBitWidth() == 16);
    CHECK(args[2]->direction == FormalArgumentDirection::Out);
    CHECK(args[3]->type->getBitWidth() == 16);
    CHECK(args[3]->direction == FormalArgumentDirection::Out);
    CHECK(args[4]->type->getBitWidth() == 1);
    CHECK(args[4]->direction == FormalArgumentDirection::InOut);

    const auto& returnStmt = foo.getBody()->as<StatementList>().list[0]->as<ReturnStatement>();
    REQUIRE(returnStmt.kind == StatementKind::Return);
    CHECK(!returnStmt.expr->bad());
    CHECK(returnStmt.expr->type->getBitWidth() == 32);

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
    const auto& cv = compilation.getRoot().topInstances[0]->memberAt<ParameterSymbol>(0).getValue();
    CHECK(cv.integer() == 4);
    NO_COMPILATION_ERRORS;
}
