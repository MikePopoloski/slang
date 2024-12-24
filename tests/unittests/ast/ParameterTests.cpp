// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/format.h>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/types/Type.h"

SVInt testParameter(const std::string& text, uint32_t index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(fullText);

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& module = *compilation.getRoot().topInstances[0];
    if (!tree->diagnostics().empty())
        WARN(report(tree->diagnostics()));

    const ParameterSymbol& param = module.body.memberAt<ParameterSymbol>(index);
    return param.getValue().integer();
}

TEST_CASE("Bind parameter") {
    CHECK(testParameter("parameter foo = 4;") == 4);
    CHECK(testParameter("parameter foo = 4 + 5;") == 9);
    CHECK(testParameter("parameter bar = 9, foo = bar + 1;", 1) == 10);
    CHECK(testParameter("parameter logic [3:0] foo = 4;") == 4);
    CHECK(testParameter("parameter logic [3:0] foo = 4'b100;") == 4);
}

TEST_CASE("Invalid param assign regress GH #420") {
    auto tree = SyntaxTree::fromText(R"(
typedef ctrl_reg_t;
parameter CTRL_RESET = $;
endpackage
module shadow # (
  RESVAL
endmodule;
shadow # (CTRL_RESET) (
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no assertion.
    compilation.getAllDiagnostics();
}

TEST_CASE("Unbounded parameters example") {
    auto tree = SyntaxTree::fromText(R"(
interface quiet_time_checker #(parameter int min_quiet = 0,
                               parameter int max_quiet = 0)
                              (input logic clk, reset_n, logic [1:0] en);
    generate
        if (!$isunbounded(max_quiet) && (max_quiet == 0)) begin
            property quiet_time;
                @(posedge clk) reset_n |-> ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        else begin
            property quiet_time;
                @(posedge clk)
                    (reset_n && ($past(en) != 0) && en == 0)
                    |->(en == 0)[*min_quiet:max_quiet]
                ##1 ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        if ((min_quiet == 0) && $isunbounded(max_quiet))
            $warning("Some warning");
    endgenerate
endinterface

interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
                         (input logic clk, reset_n, logic [1:0] expr);
    generate
        if ($isunbounded(max_cks)) begin
            property width;
                @(posedge clk)
                    (reset_n && $rose(expr)) |-> (expr [*min_cks]);
            endproperty
            a2: assert property (width);
        end
        else begin
            property width;
                @(posedge clk)
                    (reset_n && $rose(expr)) |-> (expr[*min_cks:max_cks])
                        ##1 (!expr);
            endproperty
            a2: assert property (width);
        end
    endgenerate
endinterface

module m;
    logic [1:0] enables;
    quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
    quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
    quiet_time_checker #(0, $) quiet_any (clk,1,enables);

    width_checker #(3, $) max_width_unspecified (clk,1,enables);
    width_checker #(2, 4) width_specified (clk,1,enables);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WarningTask);
}

TEST_CASE("Type parameters") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t = int, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type parameters 2") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule

module top;
    m #(longint) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type parameters 3") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule

module top;
    typedef struct packed { logic l; } asdf;
    m #(.foo_t(asdf)) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type parameters 4") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter int i = 0;
    localparam j = i;
    parameter type t = int;

    t t1 = 2;
endmodule

module top;
    m #(1, shortint) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type parameters -- bad replacement") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule

module top;
    typedef struct { logic l; } asdf;
    m #(asdf) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("Type parameters unset -- ok") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t = int, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule

module top;
    m #(.foo_t()) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type parameters unset -- bad") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t, foo_t foo = 1) ();
    if (foo) begin
        parameter type asdf = shortint, basdf = logic;
    end
endmodule

module top;
    m #(.foo_t()) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ParamHasNoValue);
}

TEST_CASE("Type parameters default -- no error") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type foo_t = bit) ();
    foo_t f;
    initial f[0] = 1;
endmodule

module top;
    m #(.foo_t(logic[3:0])) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Implicit param with unpacked dimensions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter foo[3] = '{1,2,3};
    parameter signed bar[2] = '{-1,2};
    parameter [31:0] baz[2] = '{1,2};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnpackedArrayParamType);
    CHECK(diags[1].code == diag::ConstantConversion);
}

TEST_CASE("Implicit param types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter [9:1] a = 9'b0;
    parameter b = '1;
    parameter c = 3.4;
    parameter signed d = 2'b01;
    parameter signed e = 3.4;
    parameter unsigned f = 3.4;
    parameter signed [3:5] g = 3.4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::ConstantConversion);
    CHECK(diags[2].code == diag::ConstantConversion);

    auto typeof = [&](auto name) {
        return compilation.getRoot().lookupName<ParameterSymbol>("m."s + name).getType().toString();
    };

    CHECK(typeof("a") == "logic[9:1]");
    CHECK(typeof("b") == "logic[31:0]");
    CHECK(typeof("c") == "real");
    CHECK(typeof("d") == "logic signed[1:0]");
    CHECK(typeof("e") == "logic signed[31:0]");
    CHECK(typeof("f") == "logic[31:0]");
    CHECK(typeof("g") == "logic signed[3:5]");
}

TEST_CASE("Param initialize self-reference") {
    auto tree = SyntaxTree::fromText(R"(
parameter int foo = foo;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
}

TEST_CASE("Param reference in implicit dimension specification") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter foo = 1, parameter [foo-1:0] bar = '0)();
    localparam p = bar;
endmodule

module n;
    m #(.bar(1)) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Param sum with regression GH #432") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter logic [7:0] m1 [2] = '{ 5, 10 };
    parameter int y1 = m1.sum with(item);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto cv = compilation.getRoot().lookupName<ParameterSymbol>("m.y1").getValue();
    CHECK(cv.integer() == 15);
}

TEST_CASE("Parameter port wrong / implicit type regression GH #797") {
    auto tree = SyntaxTree::fromText(R"(
module dut #(
    parameter bit P1,
    parameter bit P2
);
endmodule

module top #(
   parameter bit [3:1]
       P1 = {3{1'b1}},
       P2 = {3{1'b1}}
);
    for (genvar p=1; p<4; p++) begin: gen_loop
        dut #(.P1 (P1[p]), .P2 (P2[p])) dut_i();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter port with package scoped type regress") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    typedef int i;
endpackage

module m #(parameter int a, p::i b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter assignment missing paren compat") {
    auto tree = SyntaxTree::fromText(R"(
module a (i0, i1, o1);
    parameter B_SIZE = 8;
    input [B_SIZE-1:0] i0;
    input [B_SIZE-1:0] i1;
    output [B_SIZE-1:0] o1;

    assign o1[B_SIZE-1:0] = i0[B_SIZE-1:0] + i1[B_SIZE-1:0];
endmodule

module b(i0, i1, o1);
    input [65:0] i0;
    input [65:0] i1;
    output [65:0] o1;

    a #66 new_adder(.i0 (i0 ), .i1(i1 ), .o1(o1 ));
endmodule
)");
    CompilationOptions options;
    options.flags |= CompilationFlags::AllowBareValParamAssignment;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bsize = compilation.getRoot().lookupName<ParameterSymbol>("b.new_adder.B_SIZE");
    CHECK(bsize.getValue().integer() == 66);
}

TEST_CASE("v1800-2023: type parameter with type restriction errors") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter type enum foo, type class c)();
endmodule

class C;
endclass

module top;
    typedef struct { logic l; } asdf_t;
    m #(.foo(enum { A, B }), .c(C)) m1();
    m #(.foo(int), .c(asdf_t)) m2();
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::TypeRestrictionMismatch);
    CHECK(diags[1].code == diag::TypeRestrictionMismatch);
}

TEST_CASE("Unused param defaults are still checked for correctness") {
    auto tree = SyntaxTree::fromText(R"(
module top;
   m #(.T(int), .i(1), .j(new[3]), .k(tagged A)) m1();
endmodule

module m;
    parameter type T = struct{int i = foo;};
    parameter T i = foo;
    parameter int j[] = {};
    parameter union tagged {void A; int B;} k = tagged B foo;
    C #(3) c = new;
endmodule

class C #(parameter int i = bar);
endclass

class D #(parameter int i = bar);
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::UndeclaredIdentifier);
    CHECK(diags[3].code == diag::UndeclaredIdentifier);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Inferred parameter type with range specification -- assignment-like context") {
    auto tree = SyntaxTree::fromText(R"(
localparam [1:0][7:0] VALUES_0 = '{1, 2};
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::RecursiveDefinition);
    CHECK(diags[1].code == diag::ConstEvalParamCycle);
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
    localparam int j = foo + int'(bar == "asdf" ? baz : 0);
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
    localparam int j = foo + int'(bar == "asdf" ? baz : 0);
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

TEST_CASE("defparam target outside allowed hierarchy") {
    auto tree = SyntaxTree::fromText(R"(
module flop(input a, b, output c);
    parameter xyz = 0;
endmodule

module m(input [7:0] in, in1, output [7:0] out1);
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : somename
            flop my_flop(in[i], in1[i], out1[i]);
            if (i != 7)
                defparam somename[i+1].my_flop.xyz = i;
        end
    endgenerate
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DefparamBadHierarchy);
}

TEST_CASE("defparam target outside bind hierarchy") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    defparam n1.p = 2;
endmodule

module n;
    parameter p = 1;
endmodule

module top;
    bind top m m1();
    n n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DefparamBadHierarchy);
}

TEST_CASE("defparam with instance array ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module n(I i);
  defparam top.p = 1;
endmodule

module m;
  I i[4]();
  n n1(i[1]);
endmodule

module top;
  if (1) begin: foo
    I i();
  end
  m m1();
  parameter p = 2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DefparamBadHierarchy);
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
    REQUIRE(std::ranges::distance(root.members()) == 4);

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

TEST_CASE("Multiple defparams for one target") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter p = 1;
endmodule

module n;
    defparam m1.p = 3;
endmodule

module top;
    m m1();
    n n1();
    defparam m1.p = 2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DuplicateDefparam);
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

TEST_CASE("Param overrides within generates, arrays") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter int foo = 0;
    if (foo == 12) begin
        $info("Hello");
    end
endmodule

module top;
    m m1[8:1][2:5]();
    defparam m1[2][3].foo = 12;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InfoTask);
}

TEST_CASE("Hierarchical parameter lookup location regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    parameter int P = 6;
    function automatic int getP; return P; endfunction
endinterface

module m;
    I i();
    localparam int a = i.getP();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter type evaluation loop regress") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter I=3, W=I+1)
          (output [W-1:0] w);
    assign w = {W{1'b0}};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    for (auto param : compilation.getRoot().topInstances[0]->body.getParameters())
        param->symbol.as<ParameterSymbol>().getValue();

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter default checking spurious error regress") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter foo = '{a: 1, b: 2}, p = 1, type t = logic, bar = t[p]);
endmodule

module top;
    m #(1, 1, int, int) m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parameter default checking error regress -- GH #1009") {
    auto tree = SyntaxTree::fromText(R"(
package my_pkg;

typedef enum logic {
	CaseA
} unit_t;

typedef struct {
	unit_t val;
} struct_t;

endpackage

module param_top #(
	parameter my_pkg::struct_t Param = '{default: my_pkg::CaseA}
);
endmodule

module top;
param_top f(); // elaborates fine
param_top #(.Param('{my_pkg::CaseA})) g();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchical recursive parameter initialization") {
    auto tree = SyntaxTree::fromText(R"(
module M ();
	parameter P0  = M.P1 + 1;
	parameter P1  = M.P1 + 1;
	parameter P2  = M.P1 + 1;
	parameter P3  = M.P1 + 1;
	initial $display(P0, P1, P2, P3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RecursiveDefinition);
}

TEST_CASE("Defparam in loop regress -- GH #1081") {
    auto tree = SyntaxTree::fromText(R"(
module m1();
  parameter p = 0;
endmodule

module m2();
  genvar i;
  for (i = 0; i < 2; i = i + 1) begin : Loop1
    m1 m();
    defparam m.p = 1 + i;
  end
  for (i = 2; i < 4; i = i + 1) begin : Loop2
    m1 m();
    defparam Loop2[i].m.p = 1 + i;
  end
  for (i = 4; i < 6; i = i + 1) begin : Loop3
    m1 m();
    defparam m2.Loop3[i].m.p = 1 + i;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    for (int i = 0; i < 6; i++) {
        auto name = i < 2 ? "Loop1"sv : i < 4 ? "Loop2"sv : "Loop3"sv;
        auto& p = compilation.getRoot().lookupName<ParameterSymbol>(
            fmt::format("m2.{}[{}].m.p", name, i));
        CHECK(p.getValue().integer() == i + 1);
    }
}
