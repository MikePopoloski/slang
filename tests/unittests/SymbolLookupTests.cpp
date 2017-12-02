#include "Test.h"

#include "analysis/RootSymbol.h"
#include "parsing/SyntaxTree.h"

TEST_CASE("Explicit import lookup", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package Foo;
    parameter int x = 4;
endpackage

import Foo::x;
)");

    RootSymbol root(&tree);
    const CompilationUnitSymbol& unit = *root.compilationUnits()[0];

    LookupResult result;
    unit.lookup("x", result);
    const Symbol* x = result.getFoundSymbol();

    CHECK(result.getResultKind() == LookupResult::Found);
    CHECK(result.wasImported());
    REQUIRE(x);
    CHECK(x->kind == SymbolKind::Parameter);
    CHECK(x->as<ParameterSymbol>().value->integer() == 4);
}

TEST_CASE("Wildcard import lookup 1", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    parameter int x = 4;
endpackage

module top;
    import p::*;

    if (1) begin : gen_b
        // (1) A lookup here returns p::x
        parameter int x = 12;
        // (2) A lookup here returns local x
    end
    int x;  // If we do a lookup at (1), this becomes an error
endmodule
)");

    RootSymbol root(&tree);
    const auto& top = *root.topInstances()[0];
    const auto& gen_b = top.member<GenerateBlockSymbol>(1);
    const auto& param = gen_b.member<ParameterSymbol>(0);
    CHECK(root.compilation.diagnostics().empty());
    CHECK(param.value->integer() == 12);

    // Lookup at (2); should return the local parameter
    LookupResult result;
    result.referencePoint = LookupRefPoint::after(param);
    gen_b.lookup("x", result);
    const Symbol* symbol = result.getFoundSymbol();

    CHECK(result.getResultKind() == LookupResult::Found);
    CHECK(!result.wasImported());
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(root.compilation.diagnostics().empty());

    // Lookup at (1); should return the package parameter
    result.clear();
    result.referencePoint = LookupRefPoint::before(param);
    gen_b.lookup("x", result);
    symbol = result.getFoundSymbol();

    CHECK(result.getResultKind() == LookupResult::Found);
    // TODO: CHECK(result.wasImported());
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);

    // TODO: re-enable
    //CHECK(symbol->as<ParameterSymbol>().value().integer() == 4);
}
