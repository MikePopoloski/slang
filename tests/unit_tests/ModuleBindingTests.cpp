#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SourceManager sourceManager;
BumpAllocator alloc;
DiagnosticWriter diagWriter(sourceManager);

SyntaxTree parse(StringRef text) {
    return SyntaxTree::fromText(sourceManager, text);
}

TEST_CASE("Finding top level", "[binding:decls]") {
    auto file1 = parse("module A; A a(); endmodule\nmodule B; endmodule\nmodule C; endmodule");
    auto file2 = parse("module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&file1);
    declTable.addSyntaxTree(&file2);

    auto topLevelModules = declTable.getTopLevelModules();

    CHECK(diagnostics.empty());
    REQUIRE(topLevelModules.count() == 2);
    CHECK(topLevelModules[0]->header->name.valueText() == "D");
    CHECK(topLevelModules[1]->header->name.valueText() == "C");
}

TEST_CASE("Bind module implicit", "[binding:module_implicit]") {
    auto tree = parse(R"(
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

TEST_CASE("Module parameterization", "[binding:decls]") {
    auto tree = parse(R"(
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

}