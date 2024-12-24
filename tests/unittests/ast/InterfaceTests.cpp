// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

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

TEST_CASE("Modport port lookup location") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic a;
    modport m(input a, b);
    logic b;
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
}

TEST_CASE("Modport subroutine import") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    function void foo(int i); endfunction
    function void bar(int a, logic b); endfunction
    task baz; endtask

    modport m(import foo, import function void bar(int, logic), task baz);
endinterface

module n(I.m a);
    initial begin
        a.foo(42);
        a.bar(1, 1);
        a.baz();
    end
endmodule

module m;
    I i();
    n n1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Modport subroutine errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    function void foo; endfunction
    logic bar;
    function void asdf(int i, real r); endfunction
    modport m(input foo, import bar, baz, function int asdf(real, int), task bar);
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ExpectedImportExport);
    CHECK(diags[1].code == diag::NotASubroutine);
    CHECK(diags[2].code == diag::IfaceImportExportTarget);
    CHECK(diags[3].code == diag::MethodReturnMismatch);
    CHECK(diags[4].code == diag::NotASubroutine);
    CHECK(diags[5].code == diag::Redefinition);
}

TEST_CASE("Modport subroutine export") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    extern function void foo(int i, real r);
    extern forkjoin task t3();

    modport m(export foo, function void bar(int, logic), task baz, export func);
    modport n(import function void func(int), import task t2);
    modport o(export t2);
endinterface

module n(I.m a);
    initial begin
        a.foo(42, 3.14);
        a.bar(1, 1);
        a.baz();
    end

    function void a.bar(int i, logic l); endfunction
    task a.baz; endtask
    function void a.func(int i); endfunction

    function void a.foo(int i, real r);
    endfunction
endmodule

module m;
    I i1();
    n n1(i1);

    I i2();
    n n2(i2.m);

    localparam int baz = 3;
    task i1.t2;
        static int i = baz;
    endtask

    task i2.t2;
        static int i = baz;
    endtask
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("modport direction checking") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    wire w;
    int j;
    modport m (ref w, inout j);
    modport n (output j);
    modport o (input j);
endinterface

module m (I i);
    always_comb i.j = 1;
endmodule

module n (I.o o);
    always_comb o.j = 1;
endmodule

module top;
    I i();
    m m1(i);
    n n1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidRefArg);
    CHECK(diags[1].code == diag::InOutVarPortConn);
    CHECK(diags[2].code == diag::InputPortAssign);
}

TEST_CASE("Invalid modport clocking block") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int j;
    modport m (clocking j);
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NotAClockingBlock);
}

TEST_CASE("Explicit modport expressions") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int j, l;
    wire w;
    modport m (input .k({j, l}), output .o({l, j}), inout .p(j),
               ref .q(w), .r(foo), .s());
endinterface

module n (I.m m);
    wire [63:0] i = m.k;
    assign m.o = unsigned'(i);
    int q = m.s;
endmodule

module top;
    I i();
    n n1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InOutVarPortConn);
    CHECK(diags[1].code == diag::InvalidRefArg);
    CHECK(diags[2].code == diag::UndeclaredIdentifier);
    CHECK(diags[3].code == diag::BadAssignment);
}

TEST_CASE("Modport import subroutine consteval rules") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    function int foo(int i);
        return i;
    endfunction

    extern function int bar(int i);

    modport m(import foo, bar);
endinterface

module n (I.m m);
    localparam int j = m.foo(3);
    localparam int k = m.bar(4);

    function int m.bar(int i);
        return i;
    endfunction
endmodule

module top;
    I i();
    n n1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalSubroutineNotConstant);

    auto& j = compilation.getRoot().lookupName<ParameterSymbol>("top.n1.j");
    CHECK(j.getValue().integer() == 3);
}

TEST_CASE("Modport multi-driven errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(output i);
endinterface

module m(I.m i);
    assign i.i = 1;
endmodule

module top;
    I i();
    m m1(i), m2(i);
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
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

TEST_CASE("Selecting modport from modport-ed iface port") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(input i);
    modport n(output i);
endinterface

module o #(q) (I i);
endmodule

module m #(q) (I.m i);
    assign i.n.i = 1;
    o #(q) o1(i.n);
endmodule

module n;
    I i();
    m #(3) m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::InvalidModportAccess);
}

TEST_CASE("Connecting explicit modport on array of ifaces") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(input i);
    modport n(output i);
endinterface

module o #(q) (I i[3]);
    wire integer j = i[0].i;
endmodule

module m #(q) (I.m i[3]);
    wire integer j = i[0].i;
    o #(q) o1(i.n);
endmodule

module n #(q) (I i[3]);
    wire integer j = i[0].i;
    o #(q) o1(i.n);
endmodule

module p;
    I i [3] ();
    m #(3) m1(i.m);
    o #(3) o1(i.m);
    o #(3) o2(i.unknown);
    n #(3) n1(i.m);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::InvalidModportAccess);
    CHECK(diags[2].code == diag::NotAModport);
}

TEST_CASE("Iface array explicit modport actually restricts lookup") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    int j;
    modport m(input i);
endinterface

module m(I.m i[3]);
    int j = i[0].j;
endmodule

module n(I i[3]);
    wire integer j = i[0].j;
endmodule

module o(I.m i[4][3]);
    n n1(i[0]);
endmodule

module p;
    I i [4][3] ();
    m m1(i[0].m), m2(i[2]);
    n n1(i[1].m), n2(i[3]);
    o o1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::InvalidModportAccess);
}

TEST_CASE("Top-level module with interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I #(parameter int q = 1);
    int i, j;
    modport m(input i);
endinterface

module m(I.m i);
    if (i.q == 1) begin
        int j = i.j;
    end
endmodule

interface J #(parameter int r);
endinterface

module n(J j);
    if (j.r == 1) begin
        int j = asdf;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidModportAccess);
    CHECK(diags[1].code == diag::ParamHasNoValue);
}

TEST_CASE("Interface array multi-driven error regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(output i);
endinterface

module mod(I.m arr[3]);
    for (genvar i = 0; i < 3; i++) begin
        always_comb arr[i].i = i;
    end
endmodule

module top;
    I i [3]();
    mod m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface-based typedef") {
    auto tree = SyntaxTree::fromText(R"(
interface intf_i;
    typedef int data_t;
endinterface

module sub(intf_i p);
    typedef p.data_t my_data_t;
    my_data_t data;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& type = compilation.getRoot().lookupName<VariableSymbol>("sub.data").getType();
    CHECK(type.name == "my_data_t");
    CHECK(type.getCanonicalType().name == "int");
}

TEST_CASE("Hierarchical interface port resolution error") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m(I i);
endmodule

module othertop;
    if (1) begin : foo
        I i[3]();
    end
endmodule

module top;
    m m1(othertop.foo.i[0]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidHierarchicalIfacePortConn);
}

TEST_CASE("Wildcard connection to generic interface port") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m(interface a);
endmodule

module top;
    I a();
    m m1(.*);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WildcardPortGenericIface);
}

TEST_CASE("Top-level iface port array index regress") {
    auto tree = SyntaxTree::fromText(R"(
interface J;
    int foo;
endinterface

module m #(parameter int i = 2)(J j[i]);
    assign j[0].foo = 1;
endmodule

module n #(parameter int i = bar)(J j[i]);
    assign j[0].foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Iface array with different declared indices regress -- GH #1152") {
    auto tree = SyntaxTree::fromText(R"(
interface bus();
	logic a;
	logic b;
endinterface

module submodule(bus iface [3:2]);
	assign iface[2].a = iface[3].b;
endmodule

module top();
	bus iface[1:0]();
	submodule inst(iface);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface declaration errors") {
    auto tree = SyntaxTree::fromText(R"(
localparam type requestType = byte;
localparam type responseType = int;

interface I;
    wire r;
    modport ii(input r);
endinterface

module testMod#(N=16);
  wire clk, rst;
  I i();

  allIfc#(N) allInst(clk, rst, i, i.ii);

  virtual allIfc#(N) allInst1;
  sliceIfc sliceInst();
  virtual sliceIfc sliceInst1;
endmodule:testMod

interface automatic allIfc#(N=1)(input clk, rst, I i, I.ii i1);
  var requestType Requests[N];
  var responseType Responses[N];

  function requestType requestRead(int index);
    return Requests[index];
  endfunction

  function void responseWrite(int index, responseType response);
    Responses[index] <= response;
  endfunction

  modport clientMp(output Requests, input Responses,
                   input clk, rst);
  modport serverMp(input Requests, output Responses,
                   import requestRead, responseWrite,
                   input clk, rst);
endinterface:allIfc

interface automatic sliceIfc#(I=0)();
  interface II();
      logic reset;
  endinterface

  II ii();
  wire reset = ii.reset;

  I i();
  allIfc allInst(.clk(), .rst(), .i(i), .i1(i.ii));

  var requestType request;
  var responseType response;

  assign allInst.Requests[I] = request;
  assign response = allInst.Responses[I];

  function void requestWrite(requestType req);
    request <= req;
  endfunction

  function responseType responseRead();
    return response;
  endfunction

  wire clk = testMod.clk;  // invalid
  wire rst = testMod.rst;  // invalid

  modport clientMp(output request, input response,
                   import requestWrite, responseRead,
                   input clk, rst);
endinterface:sliceIfc
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::VirtualIfaceIfacePort);
    CHECK(diags[1].code == diag::VirtualIfaceHierRef);
}
