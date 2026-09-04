// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/expressions/MiscExpressions.h"
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
    if (i.q == 1) begin : blk
        int j = i.j;
    end
endmodule

interface J #(parameter int r);
endinterface

module n(J j);
    if (j.r == 1) begin : blk
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
  allIfc allInst(.clk(0), .rst(0), .i(i), .i1(i.ii));

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

    auto diags = compilation.getAllDiagnostics().filter(DefaultIgnoreWarnings);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::VirtualIfaceIfacePort);
    CHECK(diags[1].code == diag::VirtualIfaceHierRef);
}

TEST_CASE("Extern and export methods with instance caching") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    extern task foo;
    modport m(export foo);
    modport n(import task foo);
endinterface

module m(I.m i);
    task i.foo; endtask
endmodule

module n(I i);
    o o1(i);
endmodule

module o(I i);
    m m1(i);
endmodule

module top;
    I i1();
    n m1(i1), m2(i1);

    I i2();
    n m3(i2);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DupInterfaceExternMethod);
}

TEST_CASE("Instance caching with iface port side effects and downward names") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic l;
endinterface

module m(I i);
    assign i.l = 1;
endmodule

module o(I i);
    m m1(i);
    int a;
endmodule

module top;
    I i [3]();
    o o1(i[0]), o2(i[1]);

    assign o2.a = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Self referential interface ports") {
    auto tree = SyntaxTree::fromText(R"(
interface I(I i);
endinterface

module m;
    I i(.i(m.i));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Explicit modport expression issues") {
    auto tree = SyntaxTree::fromText(R"(
const int b = 1;

interface J(wire clk);
    clocking cb @(posedge clk);
    endclocking

    interface I(input int q);
        int a;
        modport m(input .i({a, q, b}));
        modport n(input b, clocking cb);

        struct { int i; } s;
        modport o(input .q(s.i));
    endinterface

    I i(3);
endinterface

module m;
    wire clk;
    J j(clk);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ModportMemberParent);
    CHECK(diags[1].code == diag::ModportMemberParent);
    CHECK(diags[2].code == diag::ModportMemberParent);
}

TEST_CASE("Interface containing virtual interface infinite loop regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    virtual I O;
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::VirtualInterfaceIfaceMember);
}

TEST_CASE("Interface containing virtual interface items in generate blocks") {
    auto tree = SyntaxTree::fromText(R"(
interface A;
endinterface

interface B;
endinterface

interface C #(bit P);
    if (P) begin: PSET
        virtual A intf;
    end else begin: PUNSET
        virtual B intf;
    end
endinterface

module top;
    C #(1) c();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::VirtualInterfaceIfaceMember);
}

TEST_CASE("Virtual interface member access AST") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
    logic data;
endinterface

module m;
    Iface if1(), if2();
    virtual Iface vif1 = if1, vif2 = if2;

    initial begin
        vif1.data = 1'b1;
        vif2.data = 1'b0;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    // Collect all MemberAccessExpression nodes for virtual interface member accesses.
    SmallVector<const MemberAccessExpression*> accesses;
    compilation.getRoot().visit(makeVisitor([&](auto&, const MemberAccessExpression& expr) {
        if (expr.value().type->isVirtualInterface())
            accesses.push_back(&expr);
    }));

    // There should be exactly two accesses (vif1.data and vif2.data).
    REQUIRE(accesses.size() == 2);
    auto& a0 = *accesses[0];
    auto& a1 = *accesses[1];

    // Both accesses refer to the same interface member symbol (logic data).
    CHECK(&a0.member == &a1.member);

    // But the handle expressions must point to different virtual interface variables.
    auto sym0 = a0.value().getSymbolReference();
    auto sym1 = a1.value().getSymbolReference();
    REQUIRE(sym0);
    REQUIRE(sym1);
    CHECK(sym0 != sym1);
    CHECK(sym0->name == "vif1");
    CHECK(sym1->name == "vif2");
}

TEST_CASE("Virtual interface consteval should fail") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int bar;
endinterface

function int foo;
    virtual I i;
    return i.bar;
endfunction

parameter p = foo();
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalVifType);
}

// A `$static_assert` written directly in a top-level module body can pin an interface-port
// parameter to a value/type; the override is applied to the auto-instantiated interface. The
// feature is gated on AllowTopLevelIfacePorts: without it the module can't be a top at all
// (diag::TopModuleIfacePort) and the override path never runs, so each case checks both. On the
// flag-on side we inspect the *elaborated* parameter of the connected interface to prove the
// assert actually drove the value.
TEST_CASE("Top-level iface port params from $static_assert") {
    auto compile = [](std::string_view source, bool allowIfacePorts) {
        CompilationOptions options;
        if (allowIfacePorts)
            options.flags |= CompilationFlags::AllowTopLevelIfacePorts;
        else
            options.flags &= ~CompilationFlags::AllowTopLevelIfacePorts;
        auto comp = std::make_unique<Compilation>(options);
        comp->addSyntaxTree(SyntaxTree::fromText(source));
        return comp;
    };
    auto diagCodes = [](Compilation& c) {
        std::vector<DiagCode> codes;
        for (auto& d : c.getAllDiagnostics())
            codes.push_back(d.code);
        return codes;
    };
    // The interface instance or array connected to the named interface port of the (single) top.
    auto connectedIfaceSymbol = [](Compilation& c, std::string_view portName) -> const Symbol& {
        auto& tops = c.getRoot().topInstances;
        REQUIRE(tops.size() == 1);
        for (auto conn : tops[0]->getPortConnections()) {
            if (conn->port.kind == SymbolKind::InterfacePort && conn->port.name == portName) {
                auto sym = conn->getIfaceConn().first;
                REQUIRE(sym);
                return *sym;
            }
        }
        FAIL("no connected interface instance for port");
        SLANG_UNREACHABLE;
    };
    auto connectedIface = [&](Compilation& c, std::string_view portName) -> const InstanceSymbol& {
        auto& sym = connectedIfaceSymbol(c, portName);
        REQUIRE(sym.kind == SymbolKind::Instance);
        return sym.as<InstanceSymbol>();
    };
    auto paramValue = [&](Compilation& c, std::string_view port, std::string_view param) {
        auto& sym = connectedIface(c, port).body.find(param)->as<ParameterSymbol>();
        return *sym.getValue().integer().as<int>();
    };

    // Most cases share this interface; MY_PARAM defaults to 1, making `data` a single bit.
    auto withIface = [](std::string_view body) {
        return std::string(R"(
interface my_if #(parameter int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module test_module()" + std::string(body));
    };

    SECTION("value param override past the default") {
        // MY_PARAM defaults to 1 but the assert forces it to 2, so `data[1]` is in range.
        auto src = withIface(R"(my_if my_if, output logic out);
    $static_assert(my_if.MY_PARAM == 2);
    assign out = my_if.data[1];
endmodule
)");
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 2);
        CHECK(diagCodes(*compile(src, false)) == std::vector{diag::TopModuleIfacePort});
    }

    SECTION("constant on the left") {
        auto src = withIface(R"(my_if my_if, output logic out);
    $static_assert(2 == my_if.MY_PARAM);
    assign out = my_if.data[1];
endmodule
)");
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 2);
    }

    SECTION("operand resolves in the containing module") {
        auto src = R"(
interface my_if #(parameter int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module test_module #(parameter int REQUIRED = 2)(my_if my_if, output logic out);
    $static_assert(my_if.MY_PARAM == REQUIRED);
    assign out = my_if.data[1];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 2);
    }

    SECTION("operand resolves in a package") {
        auto src = R"(
package pkg;
    parameter int REQUIRED = 2;
endpackage
interface my_if #(parameter int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module test_module(my_if my_if, output logic out);
    $static_assert(my_if.MY_PARAM == pkg::REQUIRED);
    assign out = my_if.data[1];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 2);
    }

    SECTION("one array element constrains the whole array") {
        auto src = R"(
interface my_if #(parameter int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module test_module(my_if my_if[3:2], output logic [1:0] out);
    $static_assert(my_if[2].MY_PARAM == 2);
    assign out[0] = my_if[2].data[1];
    assign out[1] = my_if[3].data[1];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());

        auto& array = connectedIfaceSymbol(*c, "my_if").as<InstanceArraySymbol>();
        REQUIRE(array.elements.size() == 2);
        auto getValue = [](const Symbol& element) {
            auto& param = element.as<InstanceSymbol>().body.find("MY_PARAM")->as<ParameterSymbol>();
            return *param.getValue().integer().as<int>();
        };
        CHECK(getValue(*array.elements[0]) == 2);
        CHECK(getValue(*array.elements[1]) == 2);
    }

    SECTION("override still bounds-checks") {
        // With MY_PARAM forced to 2, `data` is 2 bits, so an access at index 2 is still oob.
        auto src = withIface(R"(my_if my_if, output logic out);
    $static_assert(my_if.MY_PARAM == 2);
    assign out = my_if.data[2];
endmodule
)");
        auto c = compile(src, true);
        CHECK(diagCodes(*c) == std::vector{diag::IndexOOB});
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 2);
    }

    SECTION("type param override") {
        // `$static_assert(type(port.T) == type(X))` overrides the type parameter with X. DT
        // defaults to `logic` (1 bit) but is forced to pkg::my_t (8 bits), so `data[7]` is ok.
        auto src = R"(
package pkg;
    typedef logic [7:0] my_t;
endpackage
interface my_if #(parameter type DT = logic);
    DT data;
endinterface
module test_module(my_if my_if, output logic out);
    $static_assert(type(my_if.DT) == type(pkg::my_t));
    assign out = my_if.data[7];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        auto& iface = connectedIface(*c, "my_if");
        CHECK(iface.body.find("DT")->as<TypeParameterSymbol>().targetType.getType().toString() ==
              "pkg::my_t");
        CHECK(iface.body.find("data")->as<VariableSymbol>().getType().getBitWidth() == 8);

        // Without the flag DT stays `logic`, so the assert itself also fails.
        CHECK(diagCodes(*compile(src, false)) ==
              std::vector{diag::TopModuleIfacePort, diag::StaticAssert});
    }

    SECTION("multiple constraints accumulate for one port") {
        auto src = R"(
interface my_if #(parameter int P = 1, Q = 1);
    logic [P+Q-1:0] data;
endinterface
module test_module(my_if my_if, output logic out);
    $static_assert(my_if.P == 2);
    $static_assert(my_if.Q == 3);
    assign out = my_if.data[4];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c).empty());
        CHECK(paramValue(*c, "my_if", "P") == 2);
        CHECK(paramValue(*c, "my_if", "Q") == 3);
    }

    SECTION("invalid type constraint propagates") {
        auto src = R"(
interface my_if #(parameter type DT = logic);
    DT data;
endinterface
module test_module(my_if my_if);
    $static_assert(type(my_if.DT) == type(missing_t));
endmodule
)";
        auto c = compile(src, true);
        auto& dt = connectedIface(*c, "my_if").body.find("DT")->as<TypeParameterSymbol>();
        CHECK(dt.targetType.getType().isError());

        auto codes = diagCodes(*c);
        CHECK(std::ranges::find(codes, diag::UndeclaredIdentifier) != codes.end());
    }

    SECTION("unrelated assert only affects its own port") {
        auto src = withIface(R"(my_if my_if, my_if other_if, output logic out);
    $static_assert(other_if.MY_PARAM == 2);
    assign out = my_if.data[1];
endmodule
)");
        auto c = compile(src, true);
        // my_if keeps its default of 1, leaving data[1] out of range.
        CHECK(diagCodes(*c) == std::vector{diag::IndexOOB});
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 1);
        CHECK(paramValue(*c, "other_if", "MY_PARAM") == 2);
    }

    SECTION("constraint cannot depend on another interface port") {
        auto src = withIface(R"(my_if my_if, my_if other_if, output logic out);
    $static_assert(other_if.MY_PARAM == 2);
    $static_assert(my_if.MY_PARAM == other_if.MY_PARAM);
    assign out = my_if.data[1] & other_if.data[1];
endmodule
)");
        auto c = compile(src, true);
        auto codes = diagCodes(*c);
        CHECK(std::ranges::count(codes, diag::StaticAssert) == 1);
        CHECK(std::ranges::count(codes, diag::IndexOOB) == 1);
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 1);
        CHECK(paramValue(*c, "other_if", "MY_PARAM") == 2);
    }

    SECTION("localparam is not overridden") {
        auto src = R"(
interface my_if #(localparam int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module test_module(my_if my_if, output logic out);
    $static_assert(my_if.MY_PARAM == 2);
    assign out = my_if.data[1];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c) == std::vector{diag::StaticAssert, diag::IndexOOB});
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 1);
    }

    SECTION("non-const operand is skipped without spurious diagnostics") {
        // The operand `o.P` references a sibling instance's parameter, which isn't a constant we
        // can resolve when building the interface. The override is skipped (MY_PARAM stays 1, so
        // `data[1]` is oob), and we don't emit a spurious binding error: the only assert-related
        // diagnostic is the real $static_assert's own ConstEvalHierarchicalName.
        auto src = R"(
interface my_if #(parameter int MY_PARAM = 1);
    logic [MY_PARAM-1:0] data;
endinterface
module other #(parameter int P = 2);
endmodule
module test_module(my_if my_if, output logic out);
    other o();
    $static_assert(my_if.MY_PARAM == o.P);
    assign out = my_if.data[1];
endmodule
)";
        auto c = compile(src, true);
        CHECK(diagCodes(*c) == std::vector{diag::ConstEvalHierarchicalName, diag::IndexOOB});
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 1);
    }

    SECTION("assert in a generate block is ignored") {
        // Generate-block asserts are conditional on branch selection (unknown when the override
        // is applied), so they don't pin a param: MY_PARAM stays 1 and `data[1]` is oob.
        auto src = withIface(R"(my_if my_if, output logic out);
    if (1) begin : g
        $static_assert(my_if.MY_PARAM == 1);
    end
    assign out = my_if.data[1];
endmodule
)");
        auto c = compile(src, true);
        CHECK(diagCodes(*c) == std::vector{diag::IndexOOB});
        CHECK(paramValue(*c, "my_if", "MY_PARAM") == 1);
    }
}

TEST_CASE("Virtual interface instance access regress -- GH #1765") {
    auto tree = SyntaxTree::fromText(R"(
interface A;
endinterface

interface B;
    A a();
endinterface

class C;
    virtual A intf1;
    virtual B intf2;

    function set_intf(virtual B b);
        intf2 = b;
        intf1 = b.a;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Arrayed interface port cache regress -- GH #1947") {
    // NoAck has no 'ack', so on_no_ack is in error. It is written second because that is
    // the instance a shared body would hide.
    auto tree = SyntaxTree::fromText(R"(
interface HasAck;
    logic req;
    logic ack;
endinterface

interface NoAck;
    logic req;
endinterface

module Reader (interface a[2]);
    initial $display("%b", a[0].ack);
endmodule

module top;
    HasAck has_ack [2] ();
    NoAck no_ack [2] ();

    Reader on_has_ack (.a(has_ack));
    Reader on_no_ack (.a(no_ack));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CouldNotResolveHierarchicalPath);
}
