// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
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

    REQUIRE(std::ranges::distance(instance.members()) == 11);

    for (uint32_t i = 0; i < 10; i++) {
        auto& leaf = instance.memberAt<GenerateBlockSymbol>(i + 1).memberAt<InstanceSymbol>(1).body;
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

    for (i = i; i + 1 != 0; i + 1) begin end            // iter expr doesn't change genvar
    for (i = 0; i != 0; --i) begin end                  // not an error
    for (i = 0; i != 0; i++) begin end                  // not an error
    for ( = 0; i != 0; i++) begin end                   // missing genvar
    for (i = 0; i != 0; j++) begin end                  // different name in init and incr
    for (k = 0; k != 0; k++) begin end                  // missing genvar
    for (l = 0; l != 0; l++) begin end                  // l is not a genvar
    for (i = 0; i < blah.foo; i++) begin end            // non-constant stop expr
    for (i = 0; i != 0; i += blah.foo) begin end        // non-constant iter expr
    for (i = 0; us; i++) begin end                      // stop expr is not boolean
    for (i = 'x; i != 0; i++) begin end                 // unknown in init
    for (i = 0; i < 10; i += 'x) begin end              // unknown in iter
    for (i = 0; i < 10; i += 0) begin end               // repeated val
    for (i = 0; i < 10; i += integer'(arr[i+4])) name: begin end  // bad iter expr

    for (i = 0; i != 0; --i) foo: begin : baz end       // name and label

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
    coptions.flags &= ~CompilationFlags::SuppressUnused;
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
    coptions.flags &= ~CompilationFlags::SuppressUnused;

    Bag options;
    options.set(coptions);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NoTopModules);
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

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WidthTruncate);
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
    options.flags |= CompilationFlags::AllowHierarchicalConst;

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
    options.flags |= CompilationFlags::AllowHierarchicalConst;

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
    wire signed [31:0] j = i3.b;

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
    REQUIRE(std::ranges::equal(instances, std::array{"i1", "i3", "ff2", "ff1"}, {}, &Symbol::name));
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

module unused #(parameter int baz);
    $static_assert(baz < 10);
    $info("%d", baz);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bind directives") {
    auto tree = SyntaxTree::fromText(R"(
module baz(input q);
endmodule

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

    bind n baz bz(.q(b));
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

interface I;
endinterface

primitive prim(output a, input b);
    table 0 : 0;
    endtable
endprimitive

module top;
    if (1) begin: asdf
    end

    m m1();
    n n1();
    I i1();

    bind top.asdf m m1();
    bind m: top.asdf, top.m1 n n1();
    bind n: top.m1 n n1();
    bind q: top.m1 n n2();
    bind foobar n n3();
    bind n1 prim p(a, b);
    bind i1 n n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::InvalidBindTarget);
    CHECK(diags[1].code == diag::InvalidBindTarget);
    CHECK(diags[2].code == diag::WrongBindTargetDef);
    CHECK(diags[3].code == diag::Redefinition);
    CHECK(diags[4].code == diag::UnknownModule);
    CHECK(diags[5].code == diag::UnknownModule);
    CHECK(diags[6].code == diag::BindTargetPrimitive);
    CHECK(diags[7].code == diag::InvalidInstanceForParent);
}

TEST_CASE("Bind underneath another bind") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

module n;
    m m1();
endmodule

module o;
endmodule

module top;
    bind top n n1();
    bind top.n1.m1 o o1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BindUnderBind);
}

TEST_CASE("More bind examples") {
    auto tree = SyntaxTree::fromText(R"(
module Top();
    Child child1();
    Child child2();
    bind Child Sub #(1)instFoo();
endmodule

module Child();
endmodule

module Sub();
    parameter P = 0;
endmodule

module Top2();
    Child child1();
    Child child2();
    bind Top2.child1 Sub #(1)inst();
    bind Top2.child2 Sub #(2)inst();
endmodule

module unit;
endmodule

module dut;
    for (genvar i = 0; i < 16; i++) begin: units
        unit unit();
    end
endmodule

interface tb;
    wire w;
endinterface

module top;
    dut dut();
    for (genvar i = 0; i < 16; i++) begin
        bind dut.units[i].unit tb tb();
    end

    assign dut.units[2].unit.tb.w = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Binds with invalid type params") {
    auto tree = SyntaxTree::fromText(R"(
typedef enum { A, B } baz;

module m;
    typedef struct { real r; } asdf;
    typedef struct { int a; } bar;
endmodule

module n #(parameter type t, parameter type u, parameter type v);
endmodule

module top;
    m m1();

    typedef struct { int a; } asdf;
    bind top.m1 n #(asdf, bar, baz) n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    CHECK("\n" + report(diags) == R"(
source:16:21: error: bind type parameter 't' resolves to 'top.asdf' in source scope but 'm.asdf' in target scope
    bind top.m1 n #(asdf, bar, baz) n1();
                    ^~~~
source:16:27: error: bind type parameter 'u' resolves to 'bar' which cannot be found in source scope
    bind top.m1 n #(asdf, bar, baz) n1();
                          ^~~
)");
}

TEST_CASE("Complex binds and defparams example") {
    auto tree = SyntaxTree::fromText(R"(
module n;
endmodule

module o;
    parameter bar = 0;
    p #(bar) p1();
endmodule

module p #(parameter bar);
    if (bar == 1) begin
        bind top q q1();
    end

    defparam o.bar = 1;
endmodule

module q;
    wire w;
    $info("Hello");
endmodule

module r;
    parameter p = 0;
    if (p == 1) begin
        $info("World");
    end
endmodule

module top;
    parameter a = 0;
    if (a == 1) begin: foo
        n n1();
    end

    defparam top.a = 1;
    bind top.foo.n1 o o1();

    assign q1.w = 1;

    if (1) begin
        r r1();
        defparam r1.p = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InfoTask);
    CHECK(diags[1].code == diag::InfoTask);
}

TEST_CASE("Extern module missing impl errors") {
    auto tree = SyntaxTree::fromText(R"(
extern module mod1 #(parameter int i) (input real r);
extern module mod2 #(parameter int i) (input real r);
extern interface intf;

extern primitive p1 (a, b);
extern primitive p2 (a, b);

module n; endmodule

module m;
    virtual intf i;

    mod1 #(3) m1(3.14);

    bind mod2 n n1();

    p1 p(1, 2);
    p2 #3 q(1, 2);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::MissingExternModuleImpl);
    CHECK(diags[1].code == diag::MissingExternModuleImpl);
    CHECK(diags[2].code == diag::MissingExternModuleImpl);
    CHECK(diags[3].code == diag::MissingExternModuleImpl);
    CHECK(diags[4].code == diag::MissingExternModuleImpl);
}

TEST_CASE("Extern module/primitive mismatch errors") {
    auto tree = SyntaxTree::fromText(R"(
package pack; endpackage

extern module m1;
extern interface m1;

module m1();
endmodule

extern module m2 #(parameter int i = 1)(input a, interface b);
extern module m2 #(parameter int i = 2)(input a, interface b);

module automatic m2 import pack::*; #(parameter int i = 1)(input a, interface b);
endmodule

extern primitive p1(a, b);
extern primitive p1(a, b, c);

primitive p1(output a, input b);
    table 0:0; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::ExternDeclMismatchImpl);
    CHECK(diags[1].code == diag::ExternDeclMismatchPrev);
    CHECK(diags[2].code == diag::ExternDeclMismatchPrev);
    CHECK(diags[3].code == diag::ExternDeclMismatchImpl);
    CHECK(diags[4].code == diag::ExternDeclMismatchPrev);
}

TEST_CASE("Extern module/primitive redefinition errors") {
    auto tree = SyntaxTree::fromText(R"(
extern module m1;
extern primitive m1(a, b);

extern primitive p1(a, b);
extern module p1;

module p1; endmodule

primitive m1(output a, input b);
    table 0:0; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::Redefinition);
    CHECK(diags[2].code == diag::Redefinition);
    CHECK(diags[3].code == diag::Redefinition);
}

TEST_CASE("Wildcard module port list") {
    auto tree = SyntaxTree::fromText(R"(
extern module m2 #(parameter int i = 1)(input a, int b);

module m2(.*);
endmodule

extern primitive p1(a, b);

primitive p1(.*);
    output a;
    input b;
    table 0:0; endtable
endprimitive

module m;
    logic a;
    int b;
    m2 #(3) inst(a, b);
    p1 p(a, b[0]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wildcard port list errors") {
    auto tree = SyntaxTree::fromText(R"(
extern module q(.*);
extern primitive r(.*);

module m(.*);
endmodule

primitive p(.*);
    table 0:0; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExternWildcardPortList);
    CHECK(diags[1].code == diag::ExternWildcardPortList);
    CHECK(diags[2].code == diag::MissingExternWildcardPorts);
    CHECK(diags[3].code == diag::MissingExternWildcardPorts);
}

TEST_CASE("Driver in uninstantiated generate block regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int q;
    function automatic void foo(int r);
        q = r;
    endfunction
endinterface

module m #(parameter int i)(I intf);
    if (i == 1) always_comb intf.foo(1);
    else always_comb intf.foo(2);
endmodule

module top;
    I intf();
    m #(1) m1(intf);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Streaming op in uninstantiated module regress") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int i);
    foo f(.a({<< {a}}));
endmodule

module top; endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Compilation def / package retrieval API") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    module n;
    endmodule
endmodule

package p;
endpackage

primitive p2 (output reg a = 1'bx, input b, input c);
    table 00:0:0; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto defs = compilation.getDefinitions();
    REQUIRE(defs.size() == 3);
    CHECK(defs[0]->name == "m");
    CHECK(defs[1]->name == "n");
    CHECK(defs[2]->name == "p2");

    auto pkgs = compilation.getPackages();
    REQUIRE(pkgs.size() == 2);
    CHECK(pkgs[0]->name == "p");
    CHECK(pkgs[1]->name == "std");

    auto cus = compilation.getCompilationUnits();
    REQUIRE(cus.size() == 1);
    CHECK(cus[0]->members().front().name == "p");
}

TEST_CASE("Nested modules multi-driven regress") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo;
    module n;
        assign foo = 1;
    endmodule
endmodule

module top;
    m m1();
    m m2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Nested modules with infinite recursion regress") {
    auto tree = SyntaxTree::fromText(R"(
 interface I;
     I d;
     module n;
        g g;
     endmodule
 endinterface

 module top;
     I i();
 endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Check that it doesn't crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Bind corner case crash regress 1") {
    auto tree = SyntaxTree::fromText(R"(
module AL i,bind d,i AL,i
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Check that it doesn't crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Bind corner case crash regress 2") {
    auto tree = SyntaxTree::fromFileInMemory(R"(
begin
program p(a,endprogram bind p
)",
                                             SyntaxTree::getDefaultSourceManager());

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Check that it doesn't crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Bind corner case crash regress 3") {
    auto tree = SyntaxTree::fromText(R"(
module n begin
bind p program p(s
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Check that it doesn't crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Bind corner case crash regress 4") {
    auto tree = SyntaxTree::fromText(R"(
module m3;
    module m2;
        bind m2 m2 mc();
    endmodule
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DuplicateBind);
}

TEST_CASE("Nested modules with binds, parameterized, info task") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter P);
  module n;
    int i;
  endmodule
  if (P == 2) begin
  	bind n foo f();
  end
endmodule

module foo;
  $info("%m");
endmodule

module top;
  m #(1) m1();
  m #(2) m2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InfoTask);
}

TEST_CASE("Nested modules with binds, parameterized, explicit instantiation") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter P);
  module n;
    int i;
  endmodule
  if (P == 2) begin
    bind n foo f();
  end
  n n1();
endmodule

module foo;
  $info("%m");
endmodule

module top;
  m #(1) m1();
  m #(2) m2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    CHECK("\n" + report(diags) == R"(
source:13:3: note: $info encountered: top.m2.n1.f
  $info("%m");
  ^
)");
}

TEST_CASE("Virtual interface invalid due to defaram to target instance") {
    auto tree = SyntaxTree::fromText(R"(
interface J;
    parameter q = 1;
endinterface

interface I;
    J j();
endinterface

interface K;
endinterface

module m;
    I i1();
    I i2();

    virtual I vi1 = i1;
    virtual I vi2 = i2;

    defparam i1.j.q = 2;
    bind i2.j K k();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::VirtualIfaceDefparam);
    CHECK(diags[1].code == diag::VirtualIfaceDefparam);
}

TEST_CASE("Spurious errors in uninstantiated blocks, GH #1028") {
    auto tree = SyntaxTree::fromText(R"(
typedef struct packed {
  logic [7:0] r;
  logic [7:0] g;
  logic [7:0] b;
} RGB;

typedef struct packed {
  logic [7:0] c;
  logic [7:0] m;
  logic [7:0] y;
  logic [7:0] k;
} CMYK;

typedef logic [7:0] GrayScale;


virtual class ColorFunctions #(
  parameter type T_RGB  = RGB,
  parameter type T_CMYK = CMYK
);
  static function GrayScale rgb_to_grayscale(input T_RGB color);
    return (color.r * 3 + color.g * 6 + color.b * 1) / 10;
  endfunction

  static function GrayScale cmyk_to_grayscale(input T_CMYK color);
    return ((8'hFF - color.c) + (8'hFF - color.m) + (8'hFF - color.y)) / 3 * (8'hFF - color.k) / 8'hFF;
  endfunction
endclass


module GrayScaleModule #(
  parameter COLOR_SPACE = "RGB",
  type T = RGB
) (
  input T color,
  output GrayScale grayscale
);

  if (COLOR_SPACE == "RGB") begin
    assign grayscale = ColorFunctions#(.T_RGB(T))::rgb_to_grayscale(color);
  end
  else if (COLOR_SPACE == "CMYK") begin
    assign grayscale = ColorFunctions#(.T_CMYK(T))::cmyk_to_grayscale(color);
  end

endmodule


module Top (
  input RGB rgb,
  input CMYK cmyk,
  output GrayScale grayscale_rgb,
  output GrayScale grayscale_cmyk
);

  GrayScaleModule #(
    .COLOR_SPACE("RGB"),
    .T(RGB)
  ) rgb_module (
    .color(rgb),
    .grayscale(grayscale_rgb)
  );

  GrayScaleModule #(
    .COLOR_SPACE("CMYK"),
    .T(CMYK)
  ) cmyk_module (
    .color(cmyk),
    .grayscale(grayscale_cmyk)
  );

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bind with package elab loop regress -- GH #1249") {
    auto tree = SyntaxTree::fromText(R"(
module rv_plic import rv_plic_reg_pkg::*; (
    input  [63:0] c
);
endmodule

package rv_plic_reg_pkg;
    parameter int NumSrc = 64;
endpackage

module rv_plic_bind_fpv;
  bind rv_plic rv_plic_assert_fpv #(
    .P(rv_plic_reg_pkg::NumSrc)
  ) m(
    .intr_src_i(c)
  );
endmodule

module rv_plic_assert_fpv #(parameter int P = 1) (input [P-1:0] intr_src_i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Incorrect generate loop regress -- GH #1328") {
    auto tree = SyntaxTree::fromText(R"(
module Test;
  for (genvar i = 4/2; i >= 0; i--) begin
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
