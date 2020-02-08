#include "Test.h"

TEST_CASE("Finding top level") {
    auto file1 = SyntaxTree::fromText(
        "module A; endmodule\nmodule B; A a(); endmodule\nmodule C; endmodule");
    auto file2 = SyntaxTree::fromText(
        "module D; B b(); E e(); endmodule\nmodule E; module C; endmodule C c(); endmodule");

    Compilation compilation;
    compilation.addSyntaxTree(file1);
    compilation.addSyntaxTree(file2);

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
    CHECK(root.topInstances[0]->name == "C");
    CHECK(root.topInstances[1]->name == "D");
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Finding top level - 2") {
    auto tree1 = SyntaxTree::fromText(R"(
module top;
endmodule

module nottop;
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
module foo #(parameter int f = 2) ();
    if (f != 2) begin
        nottop nt();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
    CHECK(root.topInstances[0]->name == "foo");
    CHECK(root.topInstances[1]->name == "top");
}

TEST_CASE("Top level params") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int foo = 3) ();
endmodule

module NotTop #(parameter int foo) ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->name == "Top");
}

TEST_CASE("Module parameterization errors") {
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
    int bar = 9,
    localparam int baz,
    parameter bizz = baz,
    parameter int unset
    )();

    parameter int localp;

endmodule
)");

    Compilation compilation;
    auto it = evalModule(tree, compilation).membersOfType<ModuleInstanceSymbol>().begin();
    CHECK(it->name == "l1");
    it++;
    CHECK(it->name == "l2");
    it++;
    CHECK(it->name == "l3");
    it++;
    CHECK(it->name == "l4");
    it++;
    CHECK(it->name == "l5");
    it++;
    CHECK(it->name == "l6");
    it++;
    CHECK(it->name == "l7");
    it++;
    CHECK(it->name == "l8");
    it++;
    CHECK(it->name == "l9");
    it++;

    auto& diags = compilation.getSemanticDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::ParamHasNoValue);
    CHECK(diags[1].code == diag::TooManyParamAssignments);
    CHECK(diags[2].code == diag::ParamHasNoValue);
    CHECK(diags[3].code == diag::AssignedToLocalPortParam);
    CHECK(diags[4].code == diag::ParameterDoesNotExist);
    CHECK(diags[5].code == diag::AssignedToLocalBodyParam);
    CHECK(diags[6].code == diag::DuplicateParamAssignment);
    CHECK(diags[7].code == diag::MixingOrderedAndNamedParams);
    CHECK(diags[8].code == diag::LocalParamNoInitializer);
    CHECK(diags[9].code == diag::BodyParamNoInitializer);

    REQUIRE(diags[3].notes.size() == 1);
    REQUIRE(diags[5].notes.size() == 1);
    REQUIRE(diags[6].notes.size() == 1);
    CHECK(diags[3].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[5].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[6].notes[0].code == diag::NotePreviousUsage);
}

TEST_CASE("Module children (simple)") {
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

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& leaf = instance.memberAt<ModuleInstanceSymbol>(0).memberAt<ModuleInstanceSymbol>(0);
    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (conditional generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    Child child();
endmodule

module Child #(parameter foo = 4)();
    if (foo == 4) begin
        Leaf #(1) leaf();
    end
    else begin
        if (1) always_comb blaz = blob;
        Leaf #(2) leaf();
    end
endmodule

module Leaf #(parameter int foo = 4)();
    parameter localp = foo;
endmodule
)");

    Compilation compilation;
    auto& instance = evalModule(tree, compilation);
    auto& child = instance.memberAt<ModuleInstanceSymbol>(0);
    CHECK(child.memberAt<GenerateBlockSymbol>(1).isInstantiated);
    CHECK(!child.memberAt<GenerateBlockSymbol>(2).isInstantiated);

    auto& leaf = child.memberAt<GenerateBlockSymbol>(1).memberAt<ModuleInstanceSymbol>(0);
    const auto& foo = leaf.find<ParameterSymbol>("foo");
    CHECK(foo.getValue().integer() == 1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (loop generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int limit = 10)();
    for (genvar i = 0; i < limit; i += 1) begin
        Leaf #(i) leaf();
    end
endmodule

module Leaf #(parameter int foo)();
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation).memberAt<GenerateBlockArraySymbol>(1);

    REQUIRE(instance.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        const auto& leaf =
            instance.memberAt<GenerateBlockSymbol>(i).memberAt<ModuleInstanceSymbol>(1);
        const auto& foo = leaf.find<ParameterSymbol>("foo");
        CHECK(foo.getValue().integer() == i);
    }
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module children (case generate)") {
    auto tree = SyntaxTree::fromText(R"(
module Top #(parameter int val = 10)();
    case (val)
        2,3: begin : u1 end
        10: u2: begin end
    endcase
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    compilation.getRoot().lookupName<GenerateBlockSymbol>("Top.u2");
}

TEST_CASE("Interface instantiation") {
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
    logic clk;
    logic rst;

    I2CBus bus(.*);
endmodule
)");

    Compilation compilation;
    evalModule(tree, compilation);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Program instantiation") {
    auto tree = SyntaxTree::fromText(R"(
program p1 #(parameter int foo)
            (input wire clk,
             input wire rst);
    int i;
    initial begin
        i = foo;
    end
endprogram

module m;
    logic clk;
    logic rst;

    p1 #(1) bus(.*);
endmodule
)");

    Compilation compilation;
    evalModule(tree, compilation);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    parameter int blah = Foo::x;
endmodule

package Foo;
    parameter int x = 4;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    auto& cv = compilation.getRoot().topInstances[0]->memberAt<ParameterSymbol>(0).getValue();
    CHECK(cv.integer() == 4);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive parameter / function") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam logic [bar()-1:0] foo = 1;

    function logic[$bits(foo)-1:0] bar;
        return 1;
    endfunction

    localparam int baz = fun();
    localparam int bax = baz;

    function logic[bax-1:0] fun;
        return 1;
    endfunction

    localparam int a = stuff();
    localparam int b = a;

    function int stuff;
        return b;
    endfunction

    localparam int z = stuff2();
    logic [3:0] y;

    function int stuff2;
        return $bits(y);
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::RecursiveDefinition);
    CHECK(diags[1].code == diag::RecursiveDefinition);
    CHECK(diags[2].code == diag::ExpressionNotConstant);
    CHECK(diags[3].code == diag::RecursiveDefinition);
    CHECK(diags[4].code == diag::ExpressionNotConstant);
}

TEST_CASE("Parameter ordering from const func") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam int a = 1;

    function int stuff;
        return a;
    endfunction

    localparam int b = stuff;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface param from const func") {
    auto tree1 = SyntaxTree::fromText(R"(
interface I #(parameter int foo = 1);
endinterface
)");
    auto tree2 = SyntaxTree::fromText(R"(
module M(I i);
    function int stuff;
        return i.foo;
    endfunction
    
    localparam int b = stuff;
endmodule

module top;
    I i();
    M m(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface port param") {
    auto tree = SyntaxTree::fromText(R"(

interface I #(parameter int i) ();
endinterface

module M(I iface, input logic [iface.i - 1 : 0] foo);
    localparam int j = $bits(foo);
endmodule

module test;

    I #(17) i();
    M m(i, 1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto top = compilation.getRoot().topInstances[0];
    auto& j = top->find<ModuleInstanceSymbol>("m").find<ParameterSymbol>("j");
    CHECK(j.getValue().integer() == 17);
}

TEST_CASE("Generate dependent on iface port param") {
    auto tree = SyntaxTree::fromText(R"(

interface I #(parameter int i) ();
endinterface

module N;
endmodule

module M(I iface, input logic [iface.i - 1 : 0] foo);
    localparam int j = $bits(foo);
    if (j == 17) begin : asdf
        N n();
    end
endmodule

module test;

    I #(17) i();
    M m(i, 1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& asdf = compilation.getRoot().lookupName<GenerateBlockSymbol>("test.m.asdf");
    CHECK(asdf.isInstantiated);
}

TEST_CASE("Name conflict bug") {
    auto tree = SyntaxTree::fromText(R"(
module m(logic stuff);
    logic foo;
    logic[$bits(stuff)-1:0] foo;
endmodule

module n;
    m m1(.stuff(1));
endmodule
)");

    // This just tests that we don't crash.
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}

TEST_CASE("Loop generate errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    if (1) begin : blah
        int foo;
    end

    genvar i, j;
    localparam int l = 0;
    struct { logic l; } us;
    logic arr[2];

    for (i = i; i + 1; i + 1) begin end         // iter expr doesn't change genvar
    for (i = 0; i; --i) begin end               // not an error
    for (i = 0; i; i++) begin end               // not an error
    for ( = 0; i; i++) begin end                // missing genvar
    for (i = 0; i; j++) begin end               // different name in init and incr
    for (k = 0; k; k++) begin end               // missing genvar
    for (l = 0; l; l++) begin end               // l is not a genvar
    for (i = 0; i < blah.foo; i++) begin end    // non-constant stop expr
    for (i = 0; i; i += blah.foo) begin end     // non-constant iter expr
    for (i = 0; us; i++) begin end              // stop expr is not boolean
    for (i = 'x; i; i++) begin end              // unknown in init
    for (i = 0; i < 10; i += 'x) begin end      // unknown in iter
    for (i = 0; i < 10; i += 0) begin end       // repeated val
    for (i = 0; i < 10; i += arr[i+4]) name: begin end       // bad iter expr

    for (i = 0; i; --i) foo: begin : baz end    // name and label

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::NotAValue);
    CHECK((it++)->code == diag::InvalidGenvarIterExpression);
    CHECK((it++)->code == diag::ExpectedIdentifier);
    CHECK((it++)->code == diag::ExpectedGenvarIterVar);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::NotAGenvar);
    CHECK((it++)->code == diag::HierarchicalNotAllowedInConstant);
    CHECK((it++)->code == diag::HierarchicalNotAllowedInConstant);
    CHECK((it++)->code == diag::NotBooleanConvertible);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarDuplicate);
    CHECK((it++)->code == diag::ExpressionNotConstant);
    CHECK((it++)->code == diag::LabelAndName);
    CHECK(it == diags.end());
}

TEST_CASE("Case generate corner cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    case (i) endcase
    case (j) 0: begin end endcase

    case (1)
        1: begin end
        1: begin end
    endcase

    case (1)
        0: begin end
    endcase

    case (1)
        default: begin end
        default: begin end
    endcase

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::CaseGenerateEmpty);
    CHECK((it++)->code == diag::ExpressionNotConstant);
    CHECK((it++)->code == diag::UndeclaredIdentifier);
    CHECK((it++)->code == diag::CaseGenerateDup);
    CHECK((it++)->code == diag::CaseGenerateNoBlock);
    CHECK((it++)->code == diag::MultipleGenerateDefaultCases);
    CHECK(it == diags.end());
}

TEST_CASE("Conditional generate same name") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    localparam p = 2, q = 1;

    if (p == 1)
        if (q == 0) begin : u1 localparam int foo = 1; end
        else if (q == 2) begin : u1 localparam int foo = 2; end
        else ;
    else if (p == 2)
        case (q)
            0, 1, 2: begin : u1 localparam int foo = 3; end
            default: begin : u1 localparam int foo = 4; end
        endcase

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.u1.foo");
    CHECK(foo.getValue().integer() == 3);
}

TEST_CASE("Cross-CU definition lookup") {
    auto tree1 = SyntaxTree::fromText(R"(
module m #(parameter int count = 0);

    Iface ifaces[count] ();
    Blah blah(.ifaces(ifaces));

endmodule

module Blah(Iface ifaces[3]);
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
interface Iface;
endinterface
)");
    auto tree3 = SyntaxTree::fromText(R"(
module top;
    m #(3) inst ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Cross-CU package import") {
    auto tree1 = SyntaxTree::fromText(R"(
module m import pkg::*; #(parameter foo_t count = 0);
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
package pkg;
    typedef int foo_t;
endpackage
)");
    auto tree3 = SyntaxTree::fromText(R"(
module top;
    m #(3) inst ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Module/instance paths in errors") {
    auto tree = SyntaxTree::fromText(R"(
module foo;
    if (1) begin : gen
        bar b();
    end
endmodule

module bar;
    baz #(1) z1();
    baz #(2) z2();
    baz #(3) z3();
endmodule

module baz #(parameter int i)();
    if (i == 1 || i == 3) begin
        always asdf = 1;
    end
endmodule
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
  in 2 instances, e.g. foo.gen.b.z3
source:16:16: error: use of undeclared identifier 'asdf'
        always asdf = 1;
               ^~~~
)");
}

TEST_CASE("Interface array port selection") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
endinterface

module m (Iface i);
endmodule

module n (Iface arr[4]);
    for (genvar i = 0; i < 4; i++) begin
        m minst(.i(arr[i]));
    end
endmodule

module top;
    Iface arr[4] (.*);
    n ninst(.arr);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter with type imported from package") {
    auto tree1 = SyntaxTree::fromText(R"(
module m #(parameter p::foo f = "SDF") ();
    if (f == "BAR") begin: block1
        l #(.f(f)) l1();
    end
    else begin: block2
        l #(.f(f)) l1();
    end 
endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
package p;
    typedef string foo;
endpackage
)");
    auto tree3 = SyntaxTree::fromText(R"(
module l #(p::foo f) ();
endmodule
)");
    auto tree4 = SyntaxTree::fromText(R"(
module top;
    m m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree4);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Local interface not considered hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic [3:0] foo;
endinterface

module m;
    I i();
    localparam int j = $bits(i.foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& j = compilation.getRoot().lookupName<ParameterSymbol>("m.j");
    CHECK(j.getValue().integer() == 4);
}

TEST_CASE("Local interface declared later considered hierarchical") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic [3:0] foo;
endinterface

module m;
    localparam int j = $bits(i.foo);
    I i();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
}

TEST_CASE("Recursive modules -- if generate") {
    auto tree = SyntaxTree::fromText(R"(
module bar #(parameter int c) ();
    if (c == 99) bar #(99) b();
endmodule

module foo #(parameter int count = 2) ();
    if (count == 2) begin end
    else begin
        bar #(99) asdf();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive modules -- invalid") {
    auto tree = SyntaxTree::fromText(R"(
module bar;
    foo f();
endmodule

module foo #(parameter int count = 2) ();
    foo #(count * 2 + 1) f();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MaxInstanceDepthExceeded);
}

TEST_CASE("Generate loops -- too many iterations") {
    auto tree = SyntaxTree::fromText(R"(
module bar;
    for (genvar i = 0; i < 1024; i++) begin
        for (genvar j = 0; j < 1024; j++) begin
        end
    end
endmodule
)");

    // Reduce this a bit just to make the tests faster.
    CompilationOptions co;
    co.maxGenerateSteps = 8192;

    Bag options;
    options.add(co);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MaxGenerateStepsExceeded);
}

TEST_CASE("Single-unit multi-file") {
    SourceManager& sourceManager = SyntaxTree::getDefaultSourceManager();
    std::array<SourceBuffer, 2> buffers;
    buffers[0] = sourceManager.assignText("", R"(
localparam int foo = 2;

module m;
endmodule
)");

    buffers[1] = sourceManager.assignText("", R"(
module n;
    int i = foo;
endmodule
)");

    auto tree = SyntaxTree::fromBuffers(buffers, sourceManager);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    const RootSymbol& root = compilation.getRoot();
    REQUIRE(root.topInstances.size() == 2);
}