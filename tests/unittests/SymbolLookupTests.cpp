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

    const Symbol* x = unit.lookup("x");
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

    if (1) begin : b
        // (1) A lookup here returns p::x
        parameter int x = 12;
        // (2) A lookup here returns local x
    end
    int x;  // If we do a lookup at (1), this becomes an error
endmodule
)");

    DesignRootSymbol& root = *alloc.emplace<DesignRootSymbol>(tree);
    //root.topInstances()[0]->member<GenerateBlockSymbol>(0).
}


}