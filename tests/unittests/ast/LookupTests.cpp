// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
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
    ASTContext context(*unit, LookupLocation::max);
    Lookup::name(compilation.parseName("x"), context, LookupFlags::None, result);

    CHECK(result.flags.has(LookupResultFlags::WasImported));
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
    const auto& gen_b = top.body.memberAt<GenerateBlockSymbol>(1);
    const auto& param = gen_b.memberAt<ParameterSymbol>(0);
    CHECK(compilation.getSemanticDiagnostics().empty());
    CHECK(param.getValue().integer() == 12);

    // Lookup at (1); should return the local parameter
    LookupResult result;
    ASTContext context(gen_b, LookupLocation::after(param));
    Lookup::name(compilation.parseName("x"), context, LookupFlags::None, result);

    const Symbol* symbol = result.found;
    CHECK(!result.flags.has(LookupResultFlags::WasImported));
    REQUIRE(symbol);
    CHECK(symbol->kind == SymbolKind::Parameter);
    CHECK(symbol == &param);
    CHECK(compilation.getSemanticDiagnostics().empty());

    // Lookup at (2); should return the package parameter
    context.lookupIndex = LookupLocation::before(param).getIndex();
    Lookup::name(compilation.parseName("x"), context, LookupFlags::None, result);
    symbol = result.found;

    CHECK(result.flags.has(LookupResultFlags::WasImported));
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
    const auto& gen_b = top.body.memberAt<GenerateBlockSymbol>(1);

    CHECK(gen_b.find<ParameterSymbol>("foo").getValue().integer() == 4);
    CHECK(gen_b.find<ParameterSymbol>("bar").getValue().integer() == 12);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImportNameCollision);
    REQUIRE(diags[0].notes.size() == 3);
    CHECK(diags[0].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[0].notes[1].code == diag::NoteImportedFrom);
    CHECK(diags[0].notes[2].code == diag::NoteDeclarationHere);
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
    const auto& x = top.body.memberAt<GenerateBlockSymbol>(1)
                        .memberAt<ProceduralBlockSymbol>(0)
                        .getBody()
                        .as<ExpressionStatement>()
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
    const auto& x = top.body.memberAt<GenerateBlockSymbol>(2).memberAt<ParameterSymbol>(0);

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
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::DuplicateImport);
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
        automatic int x = c; // error
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
        automatic int x = c;
        import p::c; // makes line above error
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::AmbiguousWildcardImport);
    CHECK(diags[1].code == diag::Redefinition);
    CHECK(diags[2].code == diag::Redefinition);
    CHECK(diags[3].code == diag::ImportNameCollision);
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

    function automatic int baz;
        int k = foo.j;
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ConstEvalHierarchicalName);
    CHECK(diags[1].code == diag::ConstEvalHierarchicalName);
    CHECK(diags[2].code == diag::ConstEvalHierarchicalName);
    CHECK(diags[3].code == diag::ConstEvalHierarchicalName);
}

TEST_CASE("Hierarchical reference in CE across modules") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    localparam int i = foo.bar;
endmodule

module foo;
    int bar;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalHierarchicalName);
}

TEST_CASE("Lookup location for constant function call") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    typedef enum { SDF = 1 } asdf_t;
    parameter int i = foo();

    function int foo;
        return SDF;
    endfunction
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Useful error when lookup before declared in parent scope") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    int i;
    if (1) begin
        always_comb i = foo;
        type_t something;
    end

    int foo;
    typedef logic type_t;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK((it++)->code == diag::UsedBeforeDeclared);
    CHECK(it == diags.end());
}

TEST_CASE("Subroutine lookup") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    localparam int foo = 3;

    if (1) begin
        int a = foo;
        int b = foo();

        function int foo;
            return 4;
        endfunction
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& block = compilation.getRoot().topInstances[0]->body.memberAt<GenerateBlockSymbol>(1);
    EvalContext context(ASTContext(block, LookupLocation::max), EvalFlags::IsScript);
    CHECK(block.find<VariableSymbol>("a").getInitializer()->eval(context).integer() == 3);
    CHECK(block.find<VariableSymbol>("b").getInitializer()->eval(context).integer() == 4);
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

    auto& block = compilation.getRoot().topInstances[0]->body;
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

TEST_CASE("Interface array slicing") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m(I i[3]);
endmodule

module n;
    I i[8] ();
    m m1(i[1:3]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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
    always_comb array[].foo = 1;
    always_comb notArray[0].foo = 1;

    I arrayInv [-4:a] ();
    always_comb arrayInv[-4:-1][0].foo = 1;
    always_comb array[-4:-1][0].foo = 1;
    always_comb array[-4:a].foo = 1;

    always_comb array[-1:-4].foo = 1;
    always_comb array[-1+:-4].foo = 1;
    always_comb array[-1+:4].foo = 1;

    always_comb array[-2147483647-:3].foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ScopeIndexOutOfRange);
    CHECK((it++)->code == diag::InvalidScopeIndexExpression);
    CHECK((it++)->code == diag::ScopeNotIndexable);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::SelectAfterRangeSelect);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::InstanceArrayEndianMismatch);
    CHECK((it++)->code == diag::ValueMustBePositive);
    CHECK((it++)->code == diag::BadInstanceArrayRange);
    CHECK((it++)->code == diag::RangeWidthOverflow);
    CHECK(it == diags.end());
}

TEST_CASE("Generate array indexing") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    for (genvar i = 1; i < 10; i *= 2) begin : array
        logic foo;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto foo = compilation.getRoot().lookupName("m.array[8].foo");
    REQUIRE(foo);
    CHECK(foo->kind == SymbolKind::Variable);
    CHECK(foo->as<VariableSymbol>().getType().isMatching(compilation.getLogicType()));
}

TEST_CASE("Generate array indexing errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    for (genvar i = 1; i < 10; i *= 2) begin : array
        logic foo;
    end

    always_comb array[7].foo = 1;
    always_comb array[3:7].foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ScopeIndexOutOfRange);
    CHECK((it++)->code == diag::InvalidScopeIndexExpression);
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

TEST_CASE("Unit scope disambiguation") {
    auto tree = SyntaxTree::fromText(R"(
parameter int foo = 42;

module m;
    localparam int foo = 19;

    localparam int bar = foo;
    localparam int baz = $unit::foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.bar");
    CHECK(bar.getValue().integer() == 19);

    auto& baz = compilation.getRoot().lookupName<ParameterSymbol>("m.baz");
    CHECK(baz.getValue().integer() == 42);
}

TEST_CASE("Root scope disambiguation") {
    auto tree = SyntaxTree::fromText(R"(
module n;
    int f = 99;
    if (1) begin: n
        int f = 42;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& block = compilation.getRoot().lookupName<GenerateBlockSymbol>("n.n");
    auto& f1 = block.lookupName<VariableSymbol>("n.f");

    EvalContext ctx(ASTContext(block, LookupLocation::max));
    CHECK(f1.getInitializer()->eval(ctx).integer() == 42);

    auto& f2 = block.lookupName<VariableSymbol>("$root.n.f");
    CHECK(f2.getInitializer()->eval(ctx).integer() == 99);
}

TEST_CASE("Malformed name syntax") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    always_comb $unit;
    always_comb $root;
    always_comb local;
    always_comb this;
    always_comb super;
    always_comb unique;
    always_comb and;
    always_comb or;
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
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:4:22: error: invalid access token; '.' should be '::'
    always_comb $unit.foo;
                     ^
source:4:23: error: use of undeclared identifier 'foo'
    always_comb $unit.foo;
                      ^~~
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

TEST_CASE("Upward name lookup") {
    auto tree = SyntaxTree::fromText(R"(
module a;
    integer i;
    b a_b1();
endmodule

module b;
    integer i;
    c b_c1(),
      b_c2();

    initial
        b_c1.i = 2;
endmodule

module c;
    integer i;
    initial begin
        i = 1;
        b.i = 1;
    end
endmodule

module d;
    integer i;
    b d_b1();
    initial begin
        a.i = 1;
        d.i = 5;
        a.a_b1.i = 2;
        d.d_b1.i = 6;
        a.a_b1.b_c1.i = 3;
        d.d_b1.b_c1.i = 7;
        a.a_b1.b_c2.i = 4;
        d.d_b1.b_c2.i = 8;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Upward name unit scope") {
    auto file1 = SyntaxTree::fromText(R"(
module M;
    N n();

    function int foo;
        static logic f = 1;
        return 42;
    endfunction
endmodule
)");

    auto file2 = SyntaxTree::fromText(R"(
module N;
    logic f;
    always_comb f = foo.f;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(file1);
    compilation.addSyntaxTree(file2);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Name lookup from unit scope") {
    auto tree = SyntaxTree::fromText(R"(
int foo = a.baz.bar;

module a;
    if (1) begin : baz
        int bar = 0;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::StaticInitOrder);
}

TEST_CASE("Non-const name selector") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic foo;
endinterface

module M;
    I array1 [4] ();

    int i = 3;
    wire foo = array1[i].foo;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ConstEvalNonConstVariable);
    CHECK(it == diags.end());
}

TEST_CASE("Upward / downward lookup corner cases") {
    auto tree = SyntaxTree::fromText(R"(
package p1;
    logic foo;
endpackage

package p2;
    function foo; logic bar; return 1; endfunction
    function func; logic bar; return 1; endfunction
endpackage

interface I;
    logic foo;
endinterface

module top;
    M m_inst();

    function func;
        logic baz;
        return 1;
    endfunction

    if (1) begin : alias_scope
        logic bar;
    end

    if (1) begin : gen2
        logic bar;
        logic [4:0] varArray;
    end

    if (1) begin : gen3
        logic bar;
    end

    I array1 [4] ();
    I array2 [4] ();
    I array3 [4] ();

endmodule

module M;
    import p1::*;
    import p2::*;

    if (1) begin : gen1
        logic baz;
    end

    if (1) begin : gen2
        logic baz;
    end

    if (1) begin : array1
    end

    I array3 [2] ();

    typedef struct { logic [1:0] a; } type_t;
    typedef type_t alias_scope;
    type_t gen3;

    wire blah1 = m_inst.gen3.a[0];             // ok
    localparam int blah2 = int'(m_inst.gen3.a[0]);

    wire a = foo.bar;           // import collision
    wire b = asdf.bar;          // unknown identifier
    wire c = p1::bar;           // unknown member
    wire d = gen1.bar;          // no member
    wire e = func.bar;          // ok
    wire f = func.baz;          // no upward lookup because of import
    wire g = type_t.a;          // can't dot into a typedef
    wire h = alias_scope.bar;   // ok, finds top.alias_scope by upward lookup
    wire i = p3::bar;           // unknown package
    wire j = $unit::bar;        // unknown unit member
    wire k = gen2.bar;          // ok, finds top.gen2.bar
    wire l = gen3.bar;          // doesn't find top.gen3.bar because of local variable
    wire m = gen3.a[1];         // ok
    wire n = array1[0].foo;     // no upward because indexing fails
    wire o = array2[0].foo;     // ok
    wire p = array3[3].foo;     // no upward because indexing fails
    wire q = array2[].foo;      // missing expr
    wire r = .asdf;             // only parser error
    wire s = gen2.varArray[1];  // ok

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:64:33: error: reference to 'gen3' by hierarchical name is not allowed in a constant expression
    localparam int blah2 = int'(m_inst.gen3.a[0]);
                                ^~~~~~~~~~~~~~~~
source:66:14: error: multiple imports found for identifier 'foo'
    wire a = foo.bar;           // import collision
             ^~~
source:43:16: note: imported from here
    import p1::*;
               ^
source:3:11: note: declared here
    logic foo;
          ^
source:44:16: note: imported from here
    import p2::*;
               ^
source:7:14: note: declared here
    function foo; logic bar; return 1; endfunction
             ^
source:67:14: error: use of undeclared identifier 'asdf'
    wire b = asdf.bar;          // unknown identifier
             ^~~~
source:68:16: error: no member named 'bar' in package 'p1'
    wire c = p1::bar;           // unknown member
               ^ ~~~
source:69:18: error: could not resolve hierarchical path name 'bar'
    wire d = gen1.bar;          // no member
                 ^~~~
source:71:18: error: could not resolve hierarchical path name 'baz'
    wire f = func.baz;          // no upward lookup because of import
                 ^~~~
source:72:20: error: cannot use dot operator on a type name
    wire g = type_t.a;          // can't dot into a typedef
             ~~~~~~^~
source:59:39: note: declared here
    typedef struct { logic [1:0] a; } type_t;
                                      ^
source:74:14: error: unknown class or package 'p3'
    wire i = p3::bar;           // unknown package
             ^~
source:75:21: error: use of undeclared identifier 'bar'
    wire j = $unit::bar;        // unknown unit member
                    ^~~
source:77:19: error: no member named 'bar' in 'type_t'
    wire l = gen3.bar;          // doesn't find top.gen3.bar because of local variable
             ~~~~~^~~
source:79:20: error: hierarchical scope 'array1' is not indexable
    wire n = array1[0].foo;     // no upward because indexing fails
                   ^~~
source:54:20: note: declared here
    if (1) begin : array1
                   ^
source:81:21: error: hierarchical index 3 is out of scope's declared range
    wire p = array3[3].foo;     // no upward because indexing fails
                    ^
source:57:7: note: declared here
    I array3 [2] ();
      ^
source:82:20: error: invalid hierarchical index expression
    wire q = array2[].foo;      // missing expr
                   ^~
source:83:13: error: expected identifier
    wire r = .asdf;             // only parser error
            ^
)");
}

TEST_CASE("Hierarchical names in constant functions") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam int asdf = 10;

    if (1) begin : gen1
    end

    function int foo1;
        return gen1.bar;
    endfunction

    function int foo2;
        return $root.M.asdf;
    endfunction

    localparam int bar = foo1();
    localparam int baz = foo2();

    if (bar == 10) begin
        localparam int i = 99;
    end

    if (baz == 10) begin
        localparam int j = 99;
    end

    int legit;
    always_comb legit = foo2();

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:9:20: error: could not resolve hierarchical path name 'bar'
        return gen1.bar;
                   ^~~~
source:13:16: error: reference to 'asdf' by hierarchical name is not allowed in a constant expression
        return $root.M.asdf;
               ^~~~~~~~~~~~
source:17:26: note: in call to 'foo2()'
    localparam int baz = foo2();
                         ^
)");
}

TEST_CASE("Root in port connection") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    N n1($root.M.n1.foo);
    N n2(M.n1.foo);
endmodule

module N(input logic f);
    logic foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Nested block statement lookup") {
    auto tree = SyntaxTree::fromText(R"(
module M;

    initial begin
        begin
            begin : a
                int foo;
            end
        end
        begin : b
            int bar;
        end
    end

    initial begin
        a.foo = 0;
        b.bar = 1;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface array port indexing") {
    auto tree = SyntaxTree::fromText(R"(
interface I #(parameter int foo) ();
endinterface

module M(I i[4]);
    localparam int j = i[0].foo;
endmodule

module N;
    I #(.foo(9)) i[4] ();
    M m(.i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& j = compilation.getRoot().lookupName<ParameterSymbol>("N.m.j");
    CHECK(j.getValue().integer() == 9);
}

TEST_CASE("Package import in module header") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    localparam real foo = 3.14;
endpackage

package q;
    typedef enum { FOO, BAR } baz_t;
endpackage

module M import p::foo, q::*;
    #(parameter real blah = foo)
    (output baz_t b);

    always_comb b = BAR;

endmodule

module N;
    q::baz_t b;
    M m(.*);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& blah = compilation.getRoot().lookupName<ParameterSymbol>("N.m.blah");
    CHECK(blah.getValue().real() == 3.14);
}

TEST_CASE("Parameter override type lookup") {
    auto tree1 = SyntaxTree::fromText(R"(
parameter int blah = 42;
module foo #(parameter int width = 1, parameter logic[width - 1 : 0] bar, parameter int baz = blah);
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
parameter int bar = 255;
module top;
    foo #(.width(8), .bar(bar)) f();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("top.f.bar");
    CHECK(bar.getValue().integer() == 255);

    auto& baz = compilation.getRoot().lookupName<ParameterSymbol>("top.f.baz");
    CHECK(baz.getValue().integer() == 42);
}

TEST_CASE("Enums dependent on param") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int stuff) ();
    typedef enum { SDF = stuff, BAZ, BAR[2] } e1;

    int j = BAZ;
    int k = BAR1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Lookup -- type parameter ordering in module header regression") {
    auto tree = SyntaxTree::fromText(R"(
module fifo #(
    parameter int unsigned DATA_WIDTH = 32,
    parameter type dtype = logic[DATA_WIDTH - 1:0]
    )(input dtype data_i);
endmodule

module top;
    fifo f(3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid look up of definition instead of variable") {
    auto tree = SyntaxTree::fromText(R"(
module M;
endmodule

interface I;
endinterface

module N;
    int i = M + 1;
    function I asdf;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::DefinitionUsedAsValue);
    CHECK(diags[1].code == diag::DefinitionUsedAsType);
}

TEST_CASE("Lookup in invalid generate block") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int count);
    for (genvar i = 0; i < count; i++) begin: asdf
        logic foo = 0;
    end

    wire i = asdf[0].foo;
endmodule

module n;
    m #(.count(2)) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package lookup with other symbol of same name") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    logic x;
endpackage

module m;
    enum { p = 1 } sdf;
    wire i = p::x;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Lookup with typo correction") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int someInt;
endpackage

module m;
    import p::*;
    int something;
    int foo = someIn;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:9:15: error: use of undeclared identifier 'someIn'; did you mean 'someInt'?
    int foo = someIn;
              ^~~~~~
source:3:9: note: declared here
    int someInt;
        ^
)");
}

TEST_CASE("Typedef / struct member lookup bug") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef logic[1:0] asdf;
    struct { asdf a; } blah;
    localparam int i = $bits(blah.a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Error for hierarchical reference to automatic variable") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin : foo
        automatic int asdf = 1;
        asdf++;
    end
    int j = foo.asdf;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AutoVariableHierarchical);
}

TEST_CASE("Class member access") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    parameter int i = 4;
    enum { ASDF = 2 } asdf;

    int foo;
    function void bar();
        C::foo = 1;
    endfunction

    static int foo2;
    static function void bar2(); endfunction
endclass

package P;
    class D;
        typedef int bar;
    endclass
endpackage

module m #(parameter type t = P::D);
    localparam int i = C::i;
    localparam int j = C::ASDF;
    localparam P::D::bar k = 9;
    localparam t::bar l = 9;

    initial begin
        C::foo = 4;
        C::bar();

        C::foo2 = 4;
        C::bar2();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m").body;
    CHECK(m.find<ParameterSymbol>("i").getValue().integer() == 4);
    CHECK(m.find<ParameterSymbol>("j").getValue().integer() == 2);
    CHECK(m.find<ParameterSymbol>("k").getValue().integer() == 9);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NonStaticClassProperty);
    CHECK(diags[1].code == diag::NonStaticClassMethod);
}

TEST_CASE("Lookup: various corner cases and error detection") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m;
    struct { int asdf; } asdf;

    if (1) begin : block
        int foobar;
    end

    int foo = 4;
    int j = foo #(5).bar;
    int k = block.foobar #(5);
    int l = asdf.asdf #(5);

    genvar g;
    int m = g.foo;

    class C;
        int asdf;
    endclass

    int n = C[3]::foo::bar;
    int o = C::asdf::bar;
    int p = C #(5)::bar;
    int q = C::$bar;

    class G #(int i);
    endclass

    int r = G#()::foo;
    int s = $foo;

    import p::*;
    int t = unknown;

    localparam int u = $root.m.block.foobar;

    I iface();
    localparam int v = iface.bar;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 13);
    CHECK(diags[0].code == diag::NotAGenericClass);
    CHECK(diags[1].code == diag::NotAGenericClass);
    CHECK(diags[2].code == diag::NotAGenericClass);
    CHECK(diags[3].code == diag::NotAHierarchicalScope);
    CHECK(diags[4].code == diag::InvalidScopeIndexExpression);
    CHECK(diags[5].code == diag::NotAClass);
    CHECK(diags[6].code == diag::NotAGenericClass);
    CHECK(diags[7].code == diag::ExpectedIdentifier);
    CHECK(diags[8].code == diag::ParamHasNoValue);
    CHECK(diags[9].code == diag::UnknownSystemName);
    CHECK(diags[10].code == diag::UnknownPackage);
    CHECK(diags[11].code == diag::ConstEvalHierarchicalName);
    CHECK(diags[12].code == diag::CouldNotResolveHierarchicalPath);
}

TEST_CASE("Unqualified lookup for empty names") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Lookups of an empty name string should always return nullptr (not found).
    CHECK(Lookup::unqualified(compilation.getRoot(), "") == nullptr);
    CHECK(Lookup::unqualifiedAt(compilation.getRoot(), "", LookupLocation::max, {}) == nullptr);
}

TEST_CASE("Invalid array name lookups") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m;
    I ia[1 / 0] ();
    int a = ia[3];

    for (genvar i = 0; i < 10; i /= 0) begin : arr
    end
    int b = arr[3];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ValueMustNotBeUnknown);
    CHECK(diags[1].code == diag::GenvarUnknownBits);
}

TEST_CASE("Modport lookup restrictions") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic f;
    logic g;
    parameter int foo = 1;
    typedef int type_t;
    modport m(input f, type_t);
endinterface

module m(I.m i);
    wire a = i.f;
    logic b = i.g;
    logic c = i.foo;
endmodule

module top;
    I i();
    m m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NotAllowedInModport);
    CHECK(diags[1].code == diag::InvalidModportAccess);
}

TEST_CASE("Lookup into uninstantiated module") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter p);
    UnknownMod #(3) um(1,2);
endmodule

module top;
    m #(1) m1();
    initial m1.um.foo.bar = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnknownModule);
}

TEST_CASE("Hierarchical name inside unused module") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter p);
    int i = $root.foo.baz;
    int j = foo.bar.baz;
endmodule

module top;
    initial $display("hello");
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface param with unknown module") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    an_interface #() u_an_interface ();
    some_module #() u_an_instance( .the_inteface (u_an_interface) );
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnknownModule);
    CHECK(diags[1].code == diag::UnknownModule);
}

TEST_CASE("Lookup with unused selectors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic i;
    modport m(input i);
endinterface

module N (I i);
endmodule

module M;
    I i();
    N n(i.m[3]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ScopeNotIndexable);
}

TEST_CASE("Upward lookup with different resolutions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i = foo.bar;
endmodule

module n;
    m m1();
    if (1) begin : foo
        int bar;
    end
endmodule

module o;
    m m2();
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::StaticInitValue);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Package export lookup") {
    auto tree = SyntaxTree::fromText(R"(
package p1;
    int x, y;
endpackage

package p2;
    import p1::x;
    export p1::*; // exports p1::x as the name "x";
                  // p1::x and p2::x are the same declaration
endpackage

package p3;
    import p1::*;
    import p2::*;
    export p2::*;
    int q = x;
    // p1::x and q are made available from p3. Although p1::y
    // is a candidate for import, it is not actually imported
    // since it is not referenced. Since p1::y is not imported,
    // it is not made available by the export.
endpackage

package p4;
    import p1::*;
    export p1::*;

    function void foo;
        static int y = x; // p1::x is made available by the export
    endfunction
endpackage

package p5;
    import p4::*;
    import p1::*;
    export p1::x;
    export p4::x; // p4::x refers to the same declaration
                  // as p1::x so this is legal.
endpackage

package p6;
    import p1::*;
    export p1::x;
    int x; // Error. export p1::x is considered to
           // be a reference to "x" so a subsequent
           // declaration of x is illegal.
endpackage

package p7;
    int y;
endpackage

package p8;
    export *::*; // Exports both p7::y and p1::x.
    import p7::y;
    import p1::x;
endpackage

package p9;
    export foo::*;
    export p8::baz;
    export p1::x;
    export p6::x;
    export p1::x;
endpackage

package p10;
    import p1::*;
    export p6::x;
    int foo = x;
endpackage

package p11;
    import p1::*;
    int foo = x;
    export p6::x;
endpackage

package p12;
    int x;
endpackage

package p13;
    import p1::*;
    int foo = x;
    export p12::x;
endpackage

module top;
    import p2::*;
    import p4::*;
    int y = x; // x is p1::x
    int z = p5::x;
    int w = p8::y;
    int r = p3::y;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto diags = compilation.getAllDiagnostics().filter(
        {diag::StaticInitOrder, diag::StaticInitValue});
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::UnknownPackage);
    CHECK(diags[2].code == diag::UnknownPackageMember);
    CHECK(diags[3].code == diag::ImportNameCollision);
    CHECK(diags[4].code == diag::UnknownPackageMember);
}

TEST_CASE("Hierarchical lookup of type name") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    var type(n.foo) asdf = 1;
endmodule

module n;
    typedef int foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::TypeHierarchical);
}

TEST_CASE("$unit is not hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
typedef int foo;

module m;
    var type($unit::foo) asdf = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("$unit does not allow forward references") {
    auto tree = SyntaxTree::fromText(R"(
task t;
    int x;
    x = 5 + b; // illegal - "b" is defined later
    x = 5 + $unit::b; // illegal - $unit adds no special forward referencing
endtask

bit b;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
    CHECK(diags[1].code == diag::UsedBeforeDeclared);
}

TEST_CASE("Exporting an imported enum member regress") {
    auto tree = SyntaxTree::fromText(R"(
package p1;
    typedef enum { A, B } asdf_t;
endpackage

package p2;
    import p1::*;
    export p1::A;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Imported param referenced from const func") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int foo = bar();

    function int bar;
        return pkg::baz;
    endfunction
endmodule

package pkg;
    parameter int baz = 3;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid name component lookup handling") {
    auto tree = SyntaxTree::fromText(R"(
class C;
endclass

module m;
    C c;
    int i = !new;
    int k;
    initial begin
        k = c.randomize with { local::unique; };
        k = c.randomize with { local::new; };
        k = c.randomize with { local::local; };
        k = new.foo;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::UnexpectedNameToken);
    CHECK(diags[1].code == diag::UnexpectedNameToken);
    CHECK(diags[2].code == diag::ExpectedIdentifier);
    CHECK(diags[3].code == diag::ExpectedToken);
    CHECK(diags[4].code == diag::UnexpectedNameToken);
    CHECK(diags[5].code == diag::NewKeywordQualified);
}

TEST_CASE("Port / attribute lookup location regress GH #676") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m (
    clk,
    ram,
    iface
);
parameter S = "no_rw_check";

input logic clk;

(* ramstyle = S *)
output reg [31:0] ram [15:0];

(* ramstyle = S *)
I iface;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Used-before-declared opt-in corner case of self-referential symbol") {
    auto tree = SyntaxTree::fromText(R"(
parameter int i = 1;

module m;
    parameter int i = i;
endmodule

int foo;
covergroup cg;
    foo: coverpoint foo;
endgroup
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowUseBeforeDeclare;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Exception for accessing incomplete forward typedef") {
    auto tree = SyntaxTree::fromText(R"(
typedef C;
function void foo;
    C::T::bar();
endfunction

class D;
    static function void bar;
    endfunction
endclass

class C;
    typedef D T;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package cannot refer to $unit or have hierarchical ref") {
    auto tree = SyntaxTree::fromText(R"(
int i = 0;

package p;
    int j = i;
    int k = $unit::i;
    int l = m.l;

    function foo;
        static int n = bar.n;
    endfunction

    function bar;
        int n;
    endfunction
endpackage

module m;
    int l = 0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CompilationUnitFromPackage);
    CHECK(diags[1].code == diag::CompilationUnitFromPackage);
    CHECK(diags[2].code == diag::StaticInitOrder);
    CHECK(diags[3].code == diag::HierarchicalFromPackage);
}

TEST_CASE("Virtual interface access is not necessarily hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
interface Blah;
    int i;
endinterface

interface Bus;
    logic clk;
    logic a;
    clocking cb @(posedge clk);
        output a;
    endclocking

    Blah blah();
endinterface

package P;
    class BFM;
        virtual Bus intf;
        task drive_txn();
            forever begin
                @(intf.cb);
                intf.cb.a <= 1'b1;
                intf.blah.i = 1;
            end
        endtask
    endclass
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Selector of dotted interface array access") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
endinterface

module m;
    localparam int foo = 3;
    if (1) begin : asdf
        Iface i[foo]();
    end
    n #(foo) n1(asdf.i[0]);
endmodule

module n #(parameter count)(Iface i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Error for dotting into instance array") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
endmodule

module n;
    m m1[3] ();
    initial m1.i = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DotIntoInstArray);
}

TEST_CASE("Undeclared identifier -- package correction") {
    auto tree = SyntaxTree::fromText(R"(
package my_pkg;
endpackage

module m;
    int i = my_pkg;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredButFoundPackage);
}

TEST_CASE("Wildcard lookup doesn't import from packages") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int i;
endpackage

module n(input int i);
endmodule

module m;
    import p::*;
    n n1(.*);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImplicitNamedPortNotFound);
}

TEST_CASE("Wildcard lookup uses existing imports") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int i;
endpackage

module n(input int i);
endmodule

module m;
    import p::*;
    n n1(.*);

    if (1) begin
        wire integer j = i;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package self-import loop") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    export m;
    import p::*;
    K[1] t;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Check no crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Bind instantiation can't see into $unit, can't import") {
    auto tree = SyntaxTree::fromText(R"(
`default_nettype none

module m;
    import p::*;
endmodule

logic foo;
logic x;
int j;

module n #(parameter int i)
          (input logic a, b, foo);
endmodule

checker c (logic t, bar);
endchecker

package p;
    logic bar;
endpackage

module top;
    bind m n #(.i(j)) n1(.a(x), .b(bar), .foo);
    bind m c c1(.t(x), .bar);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::UndeclaredIdentifier);
    CHECK(diags[3].code == diag::ImplicitNamedPortNotFound);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
    CHECK(diags[5].code == diag::ImplicitNamedPortNotFound);
}

TEST_CASE("Enum in inherited class lookup regress -- GH #1177") {
    auto tree = SyntaxTree::fromText(R"(
package P;
    typedef class C1;

    class C2 extends C1;
        constraint c {
            if (e == A) {
            }
        }

        function f();
            enum {X, Y} z;
            z = X;
        endfunction
    endclass

    class C1;
        rand enum {A, B} e;
    endclass
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Enum initializer cycle") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum { A = 1, B = A, C = D, D = D, E = foo(), F = bar() } e;
    function foo;
        return A;
    endfunction
    function int bar;
        return F;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::EnumValueDuplicate);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::ConstEvalParamCycle);
    CHECK(diags[3].code == diag::EnumValueDuplicate);
    CHECK(diags[4].code == diag::ConstEvalParamCycle);
    CHECK(diags[5].code == diag::ConstEvalIdUsedInCEBeforeDecl);
}
