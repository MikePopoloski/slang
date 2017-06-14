#include "Catch/catch.hpp"

#include "analysis/Symbol.h"
#include "parsing/SyntaxTree.h"

using namespace slang;

namespace {

BumpAllocator alloc;

TEST_CASE("Explicit import lookup", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package Foo;
    parameter int x = 4;
endpackage

import Foo::x;
)");

    DesignRootSymbol& root = *alloc.emplace<DesignRootSymbol>(tree);
    const CompilationUnitSymbol& unit = *root.compilationUnits()[0];

    const Symbol* x = unit.lookup("x", tree.root().sourceRange().end(), LookupKind::Local);
    REQUIRE(x);
    CHECK(x->kind == SymbolKind::Parameter);
    CHECK(x->as<ParameterSymbol>().value().integer() == 4);
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

    DesignRootSymbol& root = *alloc.emplace<DesignRootSymbol>(tree);
    const auto& top = *root.topInstances()[0];
    const auto& gen_b = top.member<GenerateBlockSymbol>(1);
    const auto& param = gen_b.member<ParameterSymbol>(0);
    CHECK(root.diagnostics().empty());
    CHECK(param.value().integer() == 12);

    // Lookup at (2); should return the local parameter
    auto symbol = gen_b.lookup("x", param.location + 22, LookupKind::Local);
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(root.diagnostics().empty());

    // Lookup at (1); should return the package parameter
    symbol = gen_b.lookup("x", param.location - 2, LookupKind::Local);
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol->as<ParameterSymbol>().value().integer() == 4);

}


}