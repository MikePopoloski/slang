// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/text/SourceManager.h"

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

TEST_CASE("Duplicate module") {
    auto tree = SyntaxTree::fromText(R"(
module top #(parameter int foo = 3) ();
endmodule

module top #(parameter real r, int i) ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DuplicateDefinition);
}

TEST_CASE("Duplicate package") {
    auto tree = SyntaxTree::fromText(R"(
package pack;
endpackage

package pack;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::Redefinition);
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
    auto it = evalModule(tree, compilation).body.membersOfType<InstanceSymbol>().begin();
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
    CHECK(diags[2].code == diag::AssignedToLocalPortParam);
    CHECK(diags[3].code == diag::ParamHasNoValue);
    CHECK(diags[4].code == diag::ParameterDoesNotExist);
    CHECK(diags[5].code == diag::AssignedToLocalBodyParam);
    CHECK(diags[6].code == diag::DuplicateParamAssignment);
    CHECK(diags[7].code == diag::MixingOrderedAndNamedParams);
    CHECK(diags[8].code == diag::LocalParamNoInitializer);
    CHECK(diags[9].code == diag::BodyParamNoInitializer);

    REQUIRE(diags[2].notes.size() == 1);
    REQUIRE(diags[5].notes.size() == 1);
    REQUIRE(diags[6].notes.size() == 1);
    CHECK(diags[2].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[5].notes[0].code == diag::NoteDeclarationHere);
    CHECK(diags[6].notes[0].code == diag::NotePreviousUsage);
}

TEST_CASE("Instance missing name") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

module n;
    m();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InstanceNameRequired);
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
    const auto& instance = evalModule(tree, compilation).body;
    const auto& leaf = instance.memberAt<InstanceSymbol>(0).body.memberAt<InstanceSymbol>(0).body;
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
    auto& instance = evalModule(tree, compilation).body;
    auto& child = instance.memberAt<InstanceSymbol>(0).body;
    CHECK(!child.memberAt<GenerateBlockSymbol>(1).isUninstantiated);
    CHECK(child.memberAt<GenerateBlockSymbol>(2).isUninstantiated);

    auto& leaf = child.memberAt<GenerateBlockSymbol>(1).memberAt<InstanceSymbol>(0).body;
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
    const auto& instance = evalModule(tree, compilation).body.memberAt<GenerateBlockArraySymbol>(1);

    REQUIRE(instance.members().size() == 10);

    for (uint32_t i = 0; i < 10; i++) {
        auto& leaf = instance.memberAt<GenerateBlockSymbol>(i).memberAt<InstanceSymbol>(1).body;
        auto& foo = leaf.find<ParameterSymbol>("foo");
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
    auto& cv = compilation.getRoot().topInstances[0]->body.memberAt<ParameterSymbol>(0).getValue();
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
        return int'(y);
    endfunction

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::RecursiveDefinition);
    CHECK(diags[1].code == diag::RecursiveDefinition);
    CHECK(diags[2].code == diag::ConstEvalParamCycle);
    CHECK(diags[3].code == diag::ConstEvalIdUsedInCEBeforeDecl);
    CHECK(diags[4].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
}

TEST_CASE("Parameter ordering from const func") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    localparam int a = 1;

    function int stuff;
        return a;
    endfunction

    localparam int b = stuff();
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

    localparam int b = stuff();
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
    auto& j = top->body.find<InstanceSymbol>("m").body.find<ParameterSymbol>("j");
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
    CHECK(!asdf.isUninstantiated);
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
    CHECK((it++)->code == diag::ConstEvalHierarchicalName);
    CHECK((it++)->code == diag::ConstEvalHierarchicalName);
    CHECK((it++)->code == diag::NotBooleanConvertible);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarUnknownBits);
    CHECK((it++)->code == diag::GenvarDuplicate);
    CHECK((it++)->code == diag::ConstEvalNonConstVariable);
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
    CHECK((it++)->code == diag::ConstEvalNonConstVariable);
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
)");

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
    foo #(count + 1) f();
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
    co.maxGenerateSteps = 1024;

    Bag options;
    options.set(co);

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

TEST_CASE("Generate block external names") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    parameter genblk2 = 0;
    genvar i;

    // The following generate block is implicitly named genblk1
    if (genblk2) logic a; // top.genblk1.a
    else logic b; // top.genblk1.b

    // The following generate block is implicitly named genblk02
    // as genblk2 is already a declared identifier
    if (genblk2) logic a; // top.genblk02.a
    else logic b; // top.genblk02.b

    // The following generate block would have been named genblk3
    // but is explicitly named g1
    for (i = 0; i < 1; i = i + 1) begin : g1 // block name
        // The following generate block is implicitly named genblk1
        // as the first nested scope inside g1
        if (1) logic a; // top.g1[0].genblk1.a
    end

    // The following generate block is implicitly named genblk4 since
    // it belongs to the fourth generate construct in scope "top".
    // The previous generate block would have been
    // named genblk3 if it had not been explicitly named g1
    for (i = 0; i < 1; i = i + 1)
        // The following generate block is implicitly named genblk1
        // as the first nested generate block in genblk4
        if (1) logic a; // top.genblk4[0].genblk1.a

    // The following generate block is implicitly named genblk5
    if (1) logic a; // top.genblk5.a
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& top = compilation.getRoot().lookupName<InstanceSymbol>("top").body;
    auto range = top.membersOfType<GenerateBlockSymbol>();
    auto it = range.begin();
    CHECK((it++)->getExternalName() == "genblk1");
    it++;
    CHECK((it++)->getExternalName() == "genblk02");
    it++;
    CHECK((it++)->getExternalName() == "genblk5");

    auto& g1 = top.find<GenerateBlockArraySymbol>("g1");
    CHECK(g1.getExternalName() == "g1");
}

TEST_CASE("Error checking in uninstantiated modules") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m (input i);
endinterface

module bar #(parameter int foo);
    localparam int bar = foo;
    int j = int'(bar[foo]);
    if (j != 10) begin
        int k = j[3.4];
    end
    int k = {};

    UnknownMod #(3, 4) m(j + 1, l, {});

    I qux1();
    I qux2[3] ();
    OtherUnknown #(.a(2)) o(qux1.m, qux2);
endmodule

module top;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[1].code == diag::EmptyConcatNotAllowed);
    CHECK(diags[2].code == diag::EmptyConcatNotAllowed);
}

TEST_CASE("Manually specify top modules") {
    auto tree = SyntaxTree::fromText(R"(
module nottop;
endmodule

module invalid #(parameter int i);
endmodule

module top;
endmodule
)");

    CompilationOptions coptions;
    coptions.suppressUnused = false;
    coptions.topModules.emplace("invalid"sv);
    coptions.topModules.emplace("unknown"sv);
    coptions.topModules.emplace("top"sv);

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::UnusedDefinition);
    CHECK(diags[1].code == diag::UnusedDefinition);
    CHECK(diags[2].code == diag::InvalidTopModule);
    CHECK(diags[3].code == diag::InvalidTopModule);
}

TEST_CASE("No top warning") {
    auto tree = SyntaxTree::fromText(R"(
)");

    CompilationOptions coptions;
    coptions.suppressUnused = false;

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NoTopModules);
}

TEST_CASE("Empty parameter assignments") {
    auto tree = SyntaxTree::fromText(R"(
module n;
endmodule

module m;
    n #(,) n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ExpectedExpression);
    CHECK(diags[1].code == diag::MisplacedTrailingSeparator);
    CHECK(diags[2].code == diag::TooManyParamAssignments);
}

TEST_CASE("Options to override top-level params") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int foo, string bar, real baz);
    localparam int j = foo + (bar == "asdf" ? baz : 0);
endmodule
)");

    CompilationOptions coptions;
    coptions.paramOverrides.push_back("foo=3");
    coptions.paramOverrides.push_back("bar=\"asdf\"");
    coptions.paramOverrides.push_back("baz=1.6");

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& j = compilation.getRoot().lookupName<ParameterSymbol>("m.j");
    CHECK(j.getValue().integer() == 5);
}

TEST_CASE("Invalid param override option handling") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int foo, string bar, real baz);
    localparam int j = foo + (bar == "asdf" ? baz : 0);
endmodule
)");

    CompilationOptions coptions;
    coptions.paramOverrides.push_back("foo");
    coptions.paramOverrides.push_back("bar=");
    coptions.paramOverrides.push_back("bar=lkj");
    coptions.paramOverrides.push_back("baz=\"asdf\"");
    coptions.paramOverrides.push_back("m.baz=\"asdf\"");

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    for (size_t i = 0; i < diags.size(); i++) {
        CHECK(diags[i].code == diag::InvalidParamOverrideOpt);
    }
}

TEST_CASE("Empty params for uninstantiated modules") {
    auto tree = SyntaxTree::fromText(R"(
module top;
endmodule

module other #(parameter int bar);
    logic [3:0] asdf;
    initial asdf[bar] = 1;
endmodule

module unused #(parameter int foo = -1);
    other #(-2) inst();

    logic [3:0] baz;
    initial baz[foo] = 1;
endmodule
)");

    CompilationOptions coptions;
    coptions.topModules.emplace("top"sv);

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bind directives") {
    auto tree = SyntaxTree::fromText(R"(
module foo #(parameter int bar) (input a);
    logic b;
endmodule

module n #(parameter int f);
    logic thing;
endmodule

module m;
    localparam int j = 42;
    n #(j + 5) n1();

    initial m.n1.foo2.b <= 1;

    bind m.n1 foo #(f * 2) foo1(thing), foo2(thing);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Upward name by definition name -- design tree") {
    auto tree = SyntaxTree::fromText(R"(
module B();
    parameter w = 10;
    C c1();
endmodule

module C();
    int i = B.w;
endmodule

module top();
    B #(7) b1();
    B #(11) b2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("defparams") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    m m1();
endmodule

module m;
    parameter a = 1;
    parameter b = 2;

    logic [b-1:0] foo;

    defparam m1.a = $bits(foo) + 2;
    defparam m1.b = 4;

    if (a == 6) begin : q
        n #(5) n1();
        defparam n1.foo = 12;
    end
    defparam q.n1.bar.n2.foo = 99;
endmodule

module n #(parameter int foo = 0);
    if (foo > 10) begin : bar
        parameter baz = 6;
        n #(baz) n2();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto param = [&](auto name) {
        return compilation.getRoot().lookupName<ParameterSymbol>(name).getValue().integer();
    };

    CHECK(param("top.m1.a") == 6);
    CHECK(param("top.m1.b") == 4);
    CHECK(param("top.m1.q.n1.foo") == 12);
    CHECK(param("top.m1.q.n1.bar.n2.foo") == 99);
    CHECK(param("top.m1.q.n1.bar.n2.bar.n2.foo") == 6);
}

TEST_CASE("defparam error cases") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    m m1();
endmodule

module m;
    parameter a = 6;
    defparam q.foo = 1;

    if (a == 6) begin : q
        parameter foo = 0;
    end

    parameter b = 3;
    parameter c = 4;
    defparam b = c;
    defparam c = b;
endmodule
)");

    CompilationOptions options;
    options.maxDefParamSteps = 32;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::DefParamLocal);
    CHECK(diags[1].code == diag::DefParamCycle);
}

TEST_CASE("defparam conflicting resolution") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    m1 n();
endmodule

module m1;
    parameter p = 2;
    defparam m.n.p = 1;
    initial $display(m.n.p);
    generate
        if (p == 1) begin : m
            m2 n();
        end
    endgenerate
endmodule

module m2;
    parameter p = 3;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DefParamTargetChange);
}

TEST_CASE("defparam with cached target") {
    auto tree = SyntaxTree::fromText(R"(
module dut;
   parameter int foo = 1234;
endmodule

module main;
   dut dut0 ();
   dut #(.foo(12345)) dut1 ();

   defparam dut2.foo = 5678;
   dut dut2 ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot().topInstances[0]->body;
    REQUIRE(root.members().size() == 4);

    auto checkChild = [&](int index, const std::string& name, int val) {
        auto& inst = root.memberAt<InstanceSymbol>(index);
        CHECK(inst.name == name);

        auto& param = inst.body.memberAt<ParameterSymbol>(0);
        CHECK(param.getValue().integer() == val);
    };

    checkChild(0, "dut0", 1234);
    checkChild(1, "dut1", 12345);
    checkChild(3, "dut2", 5678);
}

TEST_CASE("defparam in infinite recursion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    m1 n();
endmodule

module m1;
    parameter p = 2;
    defparam p = 1;
    if (p == 1) begin : f
        m1 n();
    end
endmodule
)");

    CompilationOptions options;
    options.maxInstanceDepth = 8;
    options.maxDefParamSteps = 32;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MaxInstanceDepthExceeded);
}

TEST_CASE("Invalid instance parents") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

module n;
    I i();
endmodule

primitive foo(output a, input b);
    table 0 : 0;
    endtable
endprimitive

interface I;
    if (1) begin
        m m1();
    end
    foo (a, b);
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidInstanceForParent);
    CHECK(diags[1].code == diag::InvalidPrimInstanceForParent);
}

TEST_CASE("Regression test for assigning lookup indices to generate blocks") {
    auto tree = SyntaxTree::fromText(R"(
interface I; endinterface
module n (I i); endmodule

module m;
    for (genvar i = 0; i < 5; i++) begin : loop
        I iface();
        if (i == 0) begin : a
            n n1(iface);
        end
        else if (i == 1) begin : b
            n n2(iface);
        end
        else if (i == 2) begin : c
            n n3(iface);
        end
        else if (i == 3) begin : d
            n n4(iface);
        end
        else begin : e
            n n5(iface);
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Package with net assign regress GH #415") {
    auto tree = SyntaxTree::fromText(R"(
package p2;
wire varwidth = FIVE;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Assertion expressions in hierarchical instance") {
    auto tree = SyntaxTree::fromText(R"(
interface I; endinterface

module m(I i, input int j);
endmodule

module n;
    m m1(a |-> b, a [*3]);
    m m2(a throughout b, 4);
    m m3(a [*3], 4);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InvalidArgumentExpr);
    CHECK(diags[1].code == diag::InvalidArgumentExpr);
    CHECK(diags[2].code == diag::InvalidArgumentExpr);
    CHECK(diags[3].code == diag::InvalidArgumentExpr);
}

TEST_CASE("Upward name regression GH #461") {
    auto tree = SyntaxTree::fromText(R"(
module Top();
    dut_0 inst_0();
    dut_1 inst_1();
endmodule

module dut_0();
    dut inst_dut();
    dummy_1 inst_dummy();
endmodule

module dut_1();
    dut inst_dut();
    dummy_2 inst_dummy();
endmodule

module dummy_1();
    reg[1:0] data;
endmodule

module dummy_2();
    reg[7:0] data;
endmodule

module dut();
    sub inst();
endmodule

module sub();
    reg[1:0] data;
    initial begin
        data = inst_dummy.data;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WidthTruncate);
}

TEST_CASE("Parameter override regression GH #459") {
    auto tree = SyntaxTree::fromText(R"(
module tb();
    dut #(.P1(1), .P2(1), .P3(1)) inst();
endmodule

module dut();
    reg data;
    function int getv();
        return 1;
    endfunction

    parameter P0 = $bits(data);
    parameter [P0:0] P1 = 0;
    parameter [getv():0] P2 = 0;
    parameter reg [$bits(data)-1:0] P3 = 0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchical names in constexpr option") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    n #(4) n1();
    o o1();
endmodule

module n #(int i);
endmodule

module o;
    p p1();
endmodule

module p;
    parameter int foo = n1.i;
endmodule
)");

    CompilationOptions options;
    options.allowHierarchicalConst = true;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.o1.p1.foo");
    CHECK(foo.getValue().integer() == 4);
}

TEST_CASE("Hierarchical names in constexpr errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    n #(o1.p1.foo) n1();
    o o1();
endmodule

module n #(int i);
endmodule

module o;
    p p1();
endmodule

module p;
    parameter int foo = n1.i;
    specparam bar = baz();

    function baz;
        return p.bar;
    endfunction

    /*localparam enum { A = 1, B = func2(), C } asdf = C;
    localparam asdf2 = B;

    function int func2;
        return B;
    endfunction*/
endmodule
)");

    CompilationOptions options;
    options.allowHierarchicalConst = true;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConstEvalParamCycle);
    CHECK(diags[1].code == diag::ConstEvalParamCycle);
}

TEST_CASE("Hierarchical in const missing error regress") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  parameter WIDTH = dut.WIDTH;

  test dut();
endmodule

module test;
  parameter WIDTH = 8;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalHierarchicalName);
}

TEST_CASE("Nested modules") {
    auto tree = SyntaxTree::fromText(R"(
module ff2;
endmodule

module ff3 #(parameter int foo);
endmodule

module top(input d, ck, pr, clr, output q, nq);
    wire q1, nq1, nq2;
    module ff1;
        nand g1b (nq1, d, clr, q1);
        nand g1a (q1, ck, nq2, nq1);
    endmodule
    ff1 i1();

    module ff2;
        wire q2;
        nand g2b (nq2, ck, clr, q2);
        nand g2a (q2, nq1, pr, nq2);
    endmodule

    module ff3;
        int b;
        nand g3a (q, nq2, clr, nq);
        nand g3b (nq, q1, pr, q);
    endmodule
    ff3 i3();

    wire i = ff2.q2;
    wire [31:0] j = i3.b;

    module ff1; endmodule
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DuplicateDefinition);

    auto& top = compilation.getRoot().lookupName<InstanceSymbol>("top").body;
    auto instances = top.membersOfType<InstanceSymbol>();
    REQUIRE(instances.size() == 3);
    CHECK(instances[0]->name == "i1");
    CHECK(instances[1]->name == "i3");
    CHECK(instances[2]->name == "ff2");
}

TEST_CASE("Nested interfaces") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m(I i);
endmodule

module n;
    interface I; endinterface

    I i();
    m m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:12:10: error: cannot connect instance of interface 'n.I' to port of interface 'I'
    m m1(i);
         ^
source:5:12: note: declared here
module m(I i);
           ^
)");
}

TEST_CASE("Instance array size limits") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

module n;
    m m1[999999999] ();
    and a1[999999999] ();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MaxInstanceArrayExceeded);
    CHECK(diags[1].code == diag::MaxInstanceArrayExceeded);
}

TEST_CASE("defparam fork bomb mitigation") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    defparam;

    module top;
        if (1) begin
            top t1();
            top t2();
        end
    endmodule
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExpectedVariableAssignment);
    CHECK(diags[1].code == diag::MaxInstanceDepthExceeded);
}

TEST_CASE("Implicit parameter typing in instances regress GH #635") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam WIDE=32'h12345678;

    n #(.P(WIDE[31:16])) n1 ();
    n #(.P(WIDE[15:0]))  n2 ();
endmodule

module n #(parameter P=0) ();
    int i = P[15:0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m");
    auto p = &m.body.lookupName<ParameterSymbol>("n1.P");
    CHECK(p->getValue().integer() == 0x1234);

    p = &m.body.lookupName<ParameterSymbol>("n2.P");
    CHECK(p->getValue().integer() == 0x5678);
}

TEST_CASE("Top level program") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

program p(input i);
endprogram
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    REQUIRE(compilation.getRoot().topInstances.size() == 2);
    CHECK(compilation.getRoot().topInstances[1]->name == "p");
}

TEST_CASE("Accessing program objects from modules is disallowed") {
    auto tree = SyntaxTree::fromText(R"(
program p(input i);
    wire j = i;
endprogram

module m;
    wire k = p.j;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::IllegalReferenceToProgramItem);
}

TEST_CASE("Anonymous programs") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    program;
        int i;
        function int foo; return 0; endfunction
        function int bar; return 0; endfunction
    endprogram

    real foo;
endpackage

program;
    class C;
        extern function new(int r);
    endclass

    function C::new(int r);
        q.foo = p::bar();
    endfunction
endprogram

program q;
    int foo;
    C c = new(3);
endprogram

module m;
    if (1) begin
        C c = new(3);
        int j = p::bar();
    end

    import p::*;
    int j = bar();
endmodule

module n;
    import p::bar;
    int j = bar();

    $unit::C c = new(3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::NotAllowedInAnonymousProgram);
    CHECK(diags[1].code == diag::Redefinition);
    CHECK(diags[2].code == diag::IllegalReferenceToProgramItem);
    CHECK(diags[3].code == diag::IllegalReferenceToProgramItem);
    CHECK(diags[4].code == diag::IllegalReferenceToProgramItem);
    CHECK(diags[5].code == diag::IllegalReferenceToProgramItem);
    CHECK(diags[6].code == diag::IllegalReferenceToProgramItem);
}

TEST_CASE("Untaken generate block instantiation") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int i);
    $static_assert(i < 10);
endmodule

module p #(parameter int i)(input logic foo []);
    q q1(foo);
endmodule

module q(logic foo []);
endmodule

module n;
    if (1) begin
        m #(4) m1();
    end
    else begin
        m #(20) m1();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Uninstantiated virtual interface param regress GH #679") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

package P;
    class C #(type T = int);
        static function void add(string name, T t);
        endfunction
    endclass
endpackage

module M #(parameter int foo);
    I i();

    function void connect_if();
        P::C #(virtual I)::add ("intf", i);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bind directive errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

module n;
endmodule

module top;
    if (1) begin: asdf
    end

    m m1();

    bind top.asdf m m1();
    bind m: top.asdf, top.m1 n n1();
    bind n: top.m1 n n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InvalidBindTarget);
    CHECK(diags[1].code == diag::InvalidBindTarget);
    CHECK(diags[2].code == diag::WrongBindTargetDef);
    CHECK(diags[3].code == diag::Redefinition);
}
