#include "Test.h"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

TEST_CASE("Explicit import lookup") {
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
    unit->lookupName(compilation.parseName("x"), LookupLocation::max, LookupFlags::None, result);

    CHECK(result.wasImported);
    REQUIRE(result.found);
    CHECK(result.found->kind == SymbolKind::Parameter);
    CHECK(result.found->as<ParameterSymbol>().getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard import lookup 1") {
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
    gen_b.lookupName(compilation.parseName("x"), LookupLocation::after(param), LookupFlags::None,
                     result);

    const Symbol* symbol = result.found;
    CHECK(!result.wasImported);
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(compilation.getSemanticDiagnostics().empty());

    // Lookup at (2); should return the package parameter
    gen_b.lookupName(compilation.parseName("x"), LookupLocation::before(param), LookupFlags::None,
                     result);
    symbol = result.found;

    CHECK(result.wasImported);
    REQUIRE(symbol);
    REQUIRE(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol->as<ParameterSymbol>().getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard import lookup 2") {
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

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == DiagCode::ImportNameCollision);
    REQUIRE(diags[0].notes.size() == 3);
    CHECK(diags[0].notes[0].code == DiagCode::NoteDeclarationHere);
    CHECK(diags[0].notes[1].code == DiagCode::NoteImportedFrom);
    CHECK(diags[0].notes[2].code == DiagCode::NoteDeclarationHere);
}

TEST_CASE("Wildcard import lookup 3") {
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
                        .getBody()
                        ->as<ExpressionStatement>()
                        .expr.as<AssignmentExpression>()
                        .left()
                        .as<NamedValueExpression>()
                        .symbol;

    auto p_x = compilation.getPackage("p")->find("x");
    auto p2_x = compilation.getPackage("p2")->find("x");

    REQUIRE(p_x);
    REQUIRE(p2_x);
    CHECK(&x == p_x);
    CHECK(&x != p2_x);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard import lookup 4") {
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
    const auto& x = top.memberAt<GenerateBlockSymbol>(2).memberAt<ParameterSymbol>(0);

    CHECK(x.getValue().integer() == 2);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package references") {
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

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == DiagCode::UndeclaredIdentifier);
    CHECK(diags[1].code == DiagCode::UndeclaredIdentifier);
}

TEST_CASE("Package references 2") {
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

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::AmbiguousWildcardImport);
    CHECK(diags[1].code == DiagCode::RedefinitionDifferentSymbolKind);
    CHECK(diags[2].code == DiagCode::Redefinition);
    CHECK(diags[3].code == DiagCode::ImportNameCollision);
}

TEST_CASE("Member access") {
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

TEST_CASE("Hierarchical reference in CE") {
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

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == DiagCode::HierarchicalNotAllowedInConstant);
    CHECK(diags[1].code == DiagCode::HierarchicalNotAllowedInConstant);
    CHECK(diags[2].code == DiagCode::ExpressionNotConstant);
    CHECK(diags[3].code == DiagCode::HierarchicalNotAllowedInConstant);
}

TEST_CASE("Useful error when lookup before declared in parent scope") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    int i;
    if (1) begin
        always_comb i = foo;
    end

    int foo;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == DiagCode::UsedBeforeDeclared);
    CHECK(it == diags.end());
}

TEST_CASE("Subroutine lookup") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    localparam int foo = 3;

    if (1) begin
        localparam int a = foo;
        localparam int b = foo();

        function int foo;
            return 4;
        endfunction
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& block = compilation.getRoot().topInstances[0]->memberAt<GenerateBlockSymbol>(1);
    CHECK(block.find<ParameterSymbol>("a").getValue().integer() == 3);
    CHECK(block.find<ParameterSymbol>("b").getValue().integer() == 4);
}

TEST_CASE("Enum method lookup") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    typedef enum { FOO = 2, BAR = 6, BAZ } e;
    localparam e asdf = BAR;

    localparam e first = asdf.first;
    localparam e last = asdf.last();
    localparam int count1 = asdf.num;
    localparam int count2 = asdf.num();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& block = *compilation.getRoot().topInstances[0];
    CHECK(block.find<ParameterSymbol>("first").getValue().integer() == 2);
    CHECK(block.find<ParameterSymbol>("last").getValue().integer() == 7);
    CHECK(block.find<ParameterSymbol>("count1").getValue().integer() == 3);
    CHECK(block.find<ParameterSymbol>("count2").getValue().integer() == 3);
}

TEST_CASE("Instance array indexing") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic foo;
endinterface

module m;
    I array [4] ();

    always_comb array[0].foo = 1;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto foo = compilation.getRoot().lookupName("m.array[0].foo");
    REQUIRE(foo);
    CHECK(foo->kind == SymbolKind::Variable);
    CHECK(foo->as<VariableSymbol>().getType().isMatching(compilation.getLogicType()));
}

TEST_CASE("Instance array indexing errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic foo;
endinterface

module m;
    I array [-4:-1] ();

    I notArray ();

    always_comb array[0].foo = 1;
    always_comb array[-4:-3].foo = 1;
    always_comb notArray[0].foo = 1;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == DiagCode::ScopeIndexOutOfRange);
    CHECK((it++)->code == DiagCode::InvalidScopeIndexExpression);
    CHECK((it++)->code == DiagCode::ScopeNotIndexable);
    CHECK(it == diags.end());
}

TEST_CASE("Compilation scope vs instantiation scope") {
    auto file1 = SyntaxTree::fromText(R"(
parameter int foo = 42;

module m;
    N n();
endmodule
)");
    auto file2 = SyntaxTree::fromText(R"(
parameter int foo = 84;

module N;
    localparam int baz = foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(file1);
    compilation.addSyntaxTree(file2);
    NO_COMPILATION_ERRORS;

    auto baz = compilation.getRoot().lookupName("m.n.baz");
    REQUIRE(baz);
    CHECK(baz->kind == SymbolKind::Parameter);
    CHECK(baz->as<ParameterSymbol>().getValue().integer() == 84);
}

TEST_CASE("Malformed name syntax") {
    // TODO: uncomment cases below as they become supported
    auto tree = SyntaxTree::fromText(R"(
module m;

    always_comb $unit;
    always_comb $root;
    //always_comb local;
    //always_comb this;
    //always_comb super;
    always_comb unique;
    //always_comb and;
    //always_comb or;
    always_comb xor;
    always_comb new;

    always_comb asdf.$root.$unit;
    always_comb xor.xor;

    struct { logic a; logic b; } blah;
    always_comb blah.$unit;

endmodule
)");

    // This test just checks that nothing crashes.
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}

TEST_CASE("Malformed name syntax 2") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    always_comb $unit.foo;
    always_comb $root::bar;
    always_comb foo.asdf::blah;

endmodule
)",
                                     "source");

    // This test just checks that nothing crashes.
    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:4:22: error: invalid access token; '.' should be '::'
    always_comb $unit.foo;
                     ^
source:4:22: error: no member named 'foo' in compilation unit
    always_comb $unit.foo;
                     ^~~~
source:5:22: error: invalid access token; '::' should be '.'
    always_comb $root::bar;
                     ^
source:5:22: error: could not resolve hierarchical path name 'bar'
    always_comb $root::bar;
                     ^ ~~~
source:6:17: error: use of undeclared identifier 'foo'
    always_comb foo.asdf::blah;
                ^~~
source:6:25: error: invalid access token; '::' should be '.'
    always_comb foo.asdf::blah;
                        ^
)");
}