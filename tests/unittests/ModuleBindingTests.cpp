#include "Test.h"

#include <array>

#include "analysis/Symbol.h"
#include "analysis/BoundNodes.h"
#include "parsing/SyntaxTree.h"

const ModuleInstanceSymbol& evalModule(SyntaxTree& syntax) {
    DesignRootSymbol& root = *alloc.emplace<DesignRootSymbol>(&syntax);

    REQUIRE(root.topInstances().size() > 0);
    if (!syntax.diagnostics().empty())
        WARN(syntax.reportDiagnostics());

    return *root.topInstances()[0];
}

TEST_CASE("Finding top level", "[binding:decls]") {
    auto file1 = SyntaxTree::fromText("module A; A a(); endmodule\nmodule B; endmodule\nmodule C; endmodule");
    auto file2 = SyntaxTree::fromText("module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    std::array<const SyntaxTree*, 2> trees = { &file1, &file2 };
	DesignRootSymbol root(trees);

    REQUIRE(root.topInstances().size() == 2);
    CHECK(root.topInstances()[0]->name == "C");
    CHECK(root.topInstances()[1]->name == "D");
}

TEST_CASE("Bind module implicit", "[binding:modules]") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int foo = 4) ();
    Leaf l();
endmodule

module Leaf();

endmodule
)");

    evalModule(tree);
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

module Leaf #(
    int foo = 4,
    bar = 9,
    localparam baz,
    parameter bizz = baz,
    parameter unset
    )();

    parameter localp;

endmodule
)");

    // TODO:
    /*DesignRootSymbol root(tree);
    CHECK(tree.diagnostics().count() == 15);*/
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

    const auto& instance = evalModule(tree);
    const auto& leaf = instance.member<ModuleInstanceSymbol>(0).member<ModuleInstanceSymbol>(0);
    const auto& foo = leaf.module.lookup<ParameterSymbol>("foo");
    CHECK(foo.value().integer() == 4);
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

    const auto& instance = evalModule(tree);
    const auto& leaf = instance
        .member<ModuleInstanceSymbol>(0)
        .member<GenerateBlockSymbol>(1)
        .member<ModuleInstanceSymbol>(0);

    const auto& foo = leaf.module.lookup<ParameterSymbol>("foo");
    CHECK(foo.value().integer() == 1);
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

    const auto& instance = evalModule(tree);
    REQUIRE(instance.module.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        const auto& leaf = instance.member<GenerateBlockSymbol>(i).member<ModuleInstanceSymbol>(1);
        const auto& foo = leaf.module.lookup<ParameterSymbol>("foo");
        CHECK(foo.value().integer() == i);
    }
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

    const auto& instance = evalModule(tree);
    const auto& bus = instance.member<ModuleInstanceSymbol>(0);
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

    const auto& instance = evalModule(tree);
    const auto& alwaysComb = instance.member<ProceduralBlockSymbol>(2);

    CHECK(alwaysComb.procedureKind == ProceduralBlockKind::AlwaysComb);

    const auto& variable = instance.member<VariableSymbol>(4);
    CHECK(variable.type().kind == SymbolKind::IntegralType);
    CHECK(variable.name == "arr1");
}

TEST_CASE("Function declaration", "[binding:modules]") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    function static logic [15:0] foo(a, int b, output logic [15:0] u, v, inout w);
        return a + b;
    endfunction
endmodule
)");

    const auto& instance = evalModule(tree);
    const auto& foo = instance.member<SubroutineSymbol>(0);
    CHECK(!foo.isTask);
    CHECK(foo.defaultLifetime == VariableLifetime::Static);
    CHECK(foo.returnType().as<IntegralTypeSymbol>().width == 16);
    CHECK(foo.name == "foo");
    REQUIRE(foo.arguments().size() == 5);
    CHECK(foo.arguments()[0]->type().as<IntegralTypeSymbol>().width == 1);
    CHECK(foo.arguments()[0]->direction == FormalArgumentDirection::In);
    CHECK(foo.arguments()[1]->type().as<IntegralTypeSymbol>().width == 32);
    CHECK(foo.arguments()[1]->direction == FormalArgumentDirection::In);
    CHECK(foo.arguments()[2]->type().as<IntegralTypeSymbol>().width == 16);
    CHECK(foo.arguments()[2]->direction == FormalArgumentDirection::Out);
    CHECK(foo.arguments()[3]->type().as<IntegralTypeSymbol>().width == 16);
    CHECK(foo.arguments()[3]->direction == FormalArgumentDirection::Out);
    CHECK(foo.arguments()[4]->type().as<IntegralTypeSymbol>().width == 1);
    CHECK(foo.arguments()[4]->direction == FormalArgumentDirection::InOut);

    const auto& returnStmt = *(const BoundReturnStatement*)foo.body().list[0];
    REQUIRE(returnStmt.kind == BoundNodeKind::ReturnStatement);
    CHECK(!returnStmt.expr->bad());
    CHECK(returnStmt.expr->type->as<IntegralTypeSymbol>().width == 32);
}

TEST_CASE("Enum declaration", "[binding:modules]") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    enum logic [3:0] {
        A,
        B = 4,
        C
    } someVar;
endmodule
)");

    /*const auto& instance = evalModule(tree);
    const auto& someVar = instance.member<VariableSymbol>(0);
    REQUIRE(someVar.type().kind == SymbolKind::EnumType);*/
   /* REQUIRE(someVar.type->as<EnumTypeSymbol>().values.count() == 3);
    CHECK(someVar.type->as<EnumTypeSymbol>().values[0]->value.integer() == 0);
    CHECK(someVar.type->as<EnumTypeSymbol>().values[1]->value.integer() == 4);
    CHECK(someVar.type->as<EnumTypeSymbol>().values[2]->value.integer() == 5);

    const auto& b = instance.module->scope->lookup("B")->as<EnumValueSymbol>();
    CHECK(b.value.integer() == 4);*/

    // TODO: test (and implement) all the restrictions on enum and enum values
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

    DesignRootSymbol& root = *alloc.emplace<DesignRootSymbol>(&tree);
    const auto& cv = root.topInstances()[0]->member<ParameterSymbol>(0).value();
    CHECK(cv.integer() == 4);
}
