#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;

TEST_CASE("Finding top level", "[binding:decls]") {
    auto file1 = SyntaxTree::fromText("module A; A a(); endmodule\nmodule B; endmodule\nmodule C; endmodule");
    auto file2 = SyntaxTree::fromText("module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&file1);
    declTable.addSyntaxTree(&file2);

    auto topLevelModules = declTable.getTopLevelModules();

    CHECK(diagnostics.empty());
    REQUIRE(topLevelModules.count() == 2);
    CHECK(topLevelModules[0]->header->name.valueText() == "C");
    CHECK(topLevelModules[1]->header->name.valueText() == "D");
}

TEST_CASE("Bind module implicit", "[binding:modules]") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int foo = 4) ();
    Leaf l();
endmodule

module Leaf();

endmodule
)");

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);
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

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(topLevelModules[0]);

    CHECK(diagnostics.count() == 15);
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

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(topLevelModules[0]);

    CHECK(diagnostics.count() == 0);

    // Check that the tree of children has been instantiated correctly
    const auto& leaf = instance->getChild<InstanceSymbol>(0).getChild<InstanceSymbol>(0);
    const auto& foo = leaf.module->scope->lookup("foo")->as<ParameterSymbol>();

    CHECK(foo.value.integer() == 4);
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

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(topLevelModules[0]);

    CHECK(diagnostics.count() == 0);

    // Check that the tree of children has been instantiated correctly
    const auto& leaf = instance->getChild<InstanceSymbol>(0)
        .getChild<GenerateBlock>(0)
        .getChild<InstanceSymbol>(0);
    const auto& foo = leaf.module->scope->lookup("foo")->as<ParameterSymbol>();

    CHECK(foo.value.integer() == 1);
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

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(topLevelModules[0]);
    CHECK(diagnostics.count() == 0);

    // Check that the tree of children has been instantiated correctly
    REQUIRE(instance->module->children.count() == 10);

    for (int i = 0; i < 10; i++) {
        const auto& leaf = instance->getChild<GenerateBlock>(i).getChild<InstanceSymbol>(0);
        const auto& foo = leaf.module->scope->lookup("foo")->as<ParameterSymbol>();
        CHECK(foo.value.integer() == i);
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
    I2CBus bus();
endmodule
)");

    Diagnostics& diagnostics = tree.diagnostics();
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    auto topLevelModules = declTable.getTopLevelModules();
    REQUIRE(topLevelModules.count() == 1);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(topLevelModules[0]);

    if (!diagnostics.empty())
        WARN(tree.reportDiagnostics());

    const auto& bus = instance->getChild<InstanceSymbol>(0);
}

}
