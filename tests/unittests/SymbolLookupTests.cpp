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
    const auto& x = top.memberAt<GenerateBlockSymbol>(1)
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
    CHECK(diags[0].code == diag::AmbiguousWildcardImport);
    CHECK(diags[1].code == diag::RedefinitionDifferentSymbolKind);
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

    function int baz;
        int k = foo.j;
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::HierarchicalNotAllowedInConstant);
    CHECK(diags[1].code == diag::HierarchicalNotAllowedInConstant);
    CHECK(diags[2].code == diag::ExpressionNotConstant);
    CHECK(diags[3].code == diag::HierarchicalNotAllowedInConstant);
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
    CHECK(diags[0].code == diag::HierarchicalNotAllowedInConstant);
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

    auto& block = compilation.getRoot().topInstances[0]->memberAt<GenerateBlockSymbol>(1);
    EvalContext context(block, EvalFlags::IsScript);
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
    CHECK((it++)->code == diag::ScopeIndexOutOfRange);
    CHECK((it++)->code == diag::InvalidScopeIndexExpression);
    CHECK((it++)->code == diag::ScopeNotIndexable);
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
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ScopeIndexOutOfRange);
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
    CHECK(f1.getConstantValue().integer() == 42);

    auto& f2 = block.lookupName<VariableSymbol>("$root.n.f");
    CHECK(f2.getConstantValue().integer() == 99);
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
endmodule

function static int foo; logic f = 1; return 42; endfunction
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
        int bar;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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
    CHECK((it++)->code == diag::ExpressionNotConstant);
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
    localparam int blah2 = m_inst.gen3.a[0];   // undeclared identifier because const expr

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
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:64:28: error: use of undeclared identifier 'm_inst'
    localparam int blah2 = m_inst.gen3.a[0];   // undeclared identifier because const expr
                           ^~~~~~
source:64:28: note: reference to 'm_inst' by hierarchical name is not allowed in a constant expression
    localparam int blah2 = m_inst.gen3.a[0];   // undeclared identifier because const expr
                           ^
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
source:72:20: error: cannot use dot operator on a type
    wire g = type_t.a;          // can't dot into a typedef
             ~~~~~~^~
source:59:39: note: declared here
    typedef struct { logic [1:0] a; } type_t;
                                      ^
source:74:14: error: unknown class or package 'p3'
    wire i = p3::bar;           // unknown package
             ^~
source:75:19: error: no member named 'bar' in compilation unit
    wire j = $unit::bar;        // unknown unit member
                  ^ ~~~
source:77:19: error: no member named 'bar' in 'type_t'
    wire l = gen3.bar;          // doesn't find top.gen3.bar because of local variable
             ~~~~~^~~
source:79:20: error: hierarchical scope 'array1' is not indexable
    wire n = array1[0].foo;     // no upward because indexing fails
                   ^~~
source:54:12: note: declared here
    if (1) begin : array1
           ^
source:81:20: error: hierarchical index 3 is out of scope's declared range
    wire p = array3[3].foo;     // no upward because indexing fails
                   ^~~
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

    localparam int bar = foo1;
    localparam int baz = foo2;

    if (bar == 10) begin
        localparam int i = 99;
    end

    if (baz == 10) begin
        localparam int j = 99;
    end

    int legit;
    always_comb legit = foo2;

endmodule
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:9:20: error: could not resolve hierarchical path name 'bar'
        return gen1.bar;
                   ^~~~
source:16:26: note: in call to 'foo1()'
    localparam int bar = foo1;
                         ^
source:17:26: error: expression is not constant
    localparam int baz = foo2;
                         ^~~~
source:13:16: note: reference to 'asdf' by hierarchical name is not allowed in a constant expression
        return $root.M.asdf;
               ^~~~~~~~~~~~
source:17:26: note: in call to 'foo2'
    localparam int baz = foo2;
                         ^
)");
}

TEST_CASE("Root in port connection") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    N n1($root.M.n1.foo);
    N n2(M.n1.foo);
endmodule

module N(logic f);
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