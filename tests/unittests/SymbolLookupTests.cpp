#include "Test.h"

#include "binding/Lookup.h"
#include "compilation/Compilation.h"
#include "parsing/SyntaxTree.h"

TEST_CASE("Explicit import lookup", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package Foo;
    parameter int x = 4;
endpackage

import Foo::x;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const CompilationUnitSymbol* unit = compilation.getRoot().compilationUnits[0];

    LookupOperation lookup("x", *unit, SourceRange());
    const Symbol* x = lookup.getResult();

    CHECK(lookup.wasImported());
    REQUIRE(x);
    CHECK(x->kind == SymbolKind::Parameter);
    CHECK(x->as<ParameterSymbol>().getValue().integer() == 4);
}

TEST_CASE("Wildcard import lookup 1", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    parameter int x = 4;
endpackage

module top;
    import p::*;

    if (1) begin : gen_b
        // (2) A lookup here returns p::x
        parameter int x = 12;
        // (1) A lookup here returns local x
    end
    int x;  // If we do a lookup at (1), this becomes an error
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& top = *compilation.getRoot().topInstances[0];
    const auto& gen_b = top.memberAt<GenerateBlockSymbol>(1);
    const auto& param = gen_b.memberAt<ParameterSymbol>(0);
    CHECK(compilation.diagnostics().empty());
    CHECK(param.getValue().integer() == 12);

    // Lookup at (1); should return the local parameter
    LookupOperation lookup1("x", gen_b, SourceRange(), LookupContext::after(param));
    const Symbol* symbol = lookup1.getResult();

    CHECK(!lookup1.wasImported());
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(compilation.diagnostics().empty());

    // Lookup at (2); should return the package parameter
    LookupOperation lookup2("x", gen_b, SourceRange(), LookupContext::before(param));
    symbol = lookup2.getResult();

    CHECK(lookup2.wasImported());
    REQUIRE(symbol);
    REQUIRE(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol->as<ParameterSymbol>().getValue().integer() == 4);
}
