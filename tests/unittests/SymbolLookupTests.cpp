#include "Test.h"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

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

    LookupResult result;
    unit->lookupName(compilation.parseName("x"), LookupLocation::max, LookupNameKind::Variable,
                     LookupFlags::None, result);

    CHECK(result.wasImported);
    REQUIRE(result.found);
    CHECK(result.found->kind == SymbolKind::Parameter);
    CHECK(result.found->as<ParameterSymbol>().getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
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
    int x;  // If we do a lookup at (2), this becomes an error
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& top = *compilation.getRoot().topInstances[0];
    const auto& gen_b = top.memberAt<GenerateBlockSymbol>(1);
    const auto& param = gen_b.memberAt<ParameterSymbol>(0);
    CHECK(compilation.getSemanticDiagnostics().empty());
    CHECK(param.getValue().integer() == 12);

    // Lookup at (1); should return the local parameter
    LookupResult result;
    gen_b.lookupName(compilation.parseName("x"), LookupLocation::after(param), LookupNameKind::Variable,
                     LookupFlags::None, result);

    const Symbol* symbol = result.found;
    CHECK(!result.wasImported);
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(compilation.getSemanticDiagnostics().empty());

    // Lookup at (2); should return the package parameter
    gen_b.lookupName(compilation.parseName("x"), LookupLocation::before(param), LookupNameKind::Variable,
                     LookupFlags::None, result);
    symbol = result.found;

    CHECK(result.wasImported);
    REQUIRE(symbol);
    REQUIRE(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol->as<ParameterSymbol>().getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard import lookup 2", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    parameter int x = 4;
endpackage

module top;
    import p::*;

    if (1) begin : gen_b
        parameter int foo = x;
        parameter int x = 12;
        parameter int bar = x;
    end
    int x;  // Should be an error here
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& top = *compilation.getRoot().topInstances[0];
    const auto& gen_b = top.memberAt<GenerateBlockSymbol>(1);

    CHECK(gen_b.find<ParameterSymbol>("foo").getValue().integer() == 4);
    CHECK(gen_b.find<ParameterSymbol>("bar").getValue().integer() == 12);

    auto diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == DiagCode::ImportNameCollision);
    REQUIRE(diags[0].notes.size() == 3);
    CHECK(diags[0].notes[0].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[0].notes[1].code == DiagCode::NoteImportedFrom);
    CHECK(diags[0].notes[2].code == DiagCode::NoteDeclarationHere);
}

TEST_CASE("Wildcard import lookup 3", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int x;
endpackage

package p2;
    int x;
endpackage

module top;
    import p::*;
    if (1) begin : b
        initial x = 1; // Imports p::x, not p2::x
        import p2::*;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& top = *compilation.getRoot().topInstances[0];
    const auto& x = top.memberAt<GenerateBlockSymbol>(1)
                       .memberAt<ProceduralBlockSymbol>(0)
                       .getBody()->as<ExpressionStatement>()
                       .expr.as<AssignmentExpression>()
                       .left().as<NamedValueExpression>().symbol;

    auto p_x = compilation.getPackage("p")->find("x");
    auto p2_x = compilation.getPackage("p2")->find("x");

    REQUIRE(p_x);
    REQUIRE(p2_x);
    CHECK(&x == p_x);
    CHECK(&x != p2_x);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard import lookup 4", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p1;
    function int f();
        return 1;
    endfunction
endpackage

package p2;
    function int f();
        return 2;
    endfunction
endpackage

module top;
    import p2::*;
    int x;
    if (1) begin : b
        parameter int x = f();
    end
    import p1::*;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& top = *compilation.getRoot().topInstances[0];
    const auto& x = top.memberAt<GenerateBlockSymbol>(2)
                       .memberAt<ParameterSymbol>(0);

    CHECK(x.getValue().integer() == 2);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package references", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package ComplexPkg;
    typedef struct packed {shortint i, r;} Complex;

    typedef enum { FALSE, TRUE } bool_t;
endpackage

module top;
    parameter ComplexPkg::Complex blah1 = '0;

    parameter Complex blah2 = '0; // causes an error

    import ComplexPkg::Complex;
    parameter Complex blah3 = '0; // no error

    // Importing an enum type doesn't import the enumerands
    import ComplexPkg::bool_t;
    bool_t b;
    initial begin
        b = ComplexPkg::   FALSE; // ok
        b = FALSE; // error
    end

    initial begin
        import ComplexPkg::FALSE;
        import ComplexPkg::FALSE;
        b = FALSE;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    Diagnostics diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == DiagCode::UndeclaredIdentifier);
    CHECK(diags[1].code == DiagCode::UndeclaredIdentifier);
}

TEST_CASE("Package references 2", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    typedef enum { FALSE, TRUE } BOOL;
    const BOOL c = FALSE;
endpackage

package q;
    const int c = 0;
endpackage

module m1;
    initial begin
        import p::*;
        import q::*;
    end

    initial begin
        import p::*;
        import q::*;
        int x = c; // error
    end
endmodule

module m2;
    initial begin
        int c;
        import p::c; // error
    end

    initial begin
        import p::c;
        import q::c; // error
    end

    initial begin
        import q::*;
        int x = c;
        import p::c; // makes line above error
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    Diagnostics diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::AmbiguousWildcardImport);
    CHECK(diags[1].code == DiagCode::RedefinitionDifferentSymbolKind);
    CHECK(diags[2].code == DiagCode::Redefinition);
    CHECK(diags[3].code == DiagCode::ImportNameCollision);
}

TEST_CASE("Member access", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { logic a; logic b; } foo;

    initial begin
        foo.a = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchical reference in CE", "[symbols:lookup]") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    if (1) begin : foo
        int i;
        parameter int j = 3;
    end

    localparam int j = foo.i;
    if (foo.i) begin
        int j = asdf;
    end

    localparam int k = baz();

    function logic[foo.i-1:0] bar;
        foo.i = 1; // fine if not called from constant context, otherwise an error
    endfunction

    function int baz;
        int k = foo.j;
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    Diagnostics diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::HierarchicalNotAllowedInConstant);
    CHECK(diags[1].code == DiagCode::HierarchicalNotAllowedInConstant);
    CHECK(diags[2].code == DiagCode::ExpressionNotConstant);
    CHECK(diags[3].code == DiagCode::HierarchicalNotAllowedInConstant);
}