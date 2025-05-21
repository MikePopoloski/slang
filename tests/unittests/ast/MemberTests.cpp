// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Statement.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"

TEST_CASE("Nets") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    wire logic f = 1;
    wire #5 g;
    wire logic #(1:2:3, 3:2:1, 1:2:1) h;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid nets") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire int i = 1;
    wire real r = 3.1;
    wire struct { real r; } s;
    wire vectored v;

    logic foo[2];
    wire #(1,b) asdf;
    wire #(1, foo) asdf2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidNetType);
    CHECK(diags[1].code == diag::InvalidNetType);
    CHECK(diags[2].code == diag::InvalidNetType);
    CHECK(diags[3].code == diag::SingleBitVectored);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
    CHECK(diags[5].code == diag::DelayNotNumeric);
}

TEST_CASE("Net types can be unpacked unions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef union { logic l; } u;
    wire u w;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bad signed specifier") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    bit signed;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExpectedDeclarator);
}

TEST_CASE("Continuous Assignments") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    wire foo;
    assign foo = 1, foo = 'z;

    wire bar;
    assign (strong1, supply0) #(3,2,1) bar = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Continuous assign same implicit net") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    assign a = 1, a = 0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid continuous assign") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
endinterface

module m;
    logic foo[3];
    wire i;
    assign #(foo) i = 1;

    int j;
    logic [7:0] baz;
    assign foo[j] = 1;
    assign baz[j+:3] = '0;

    class C;
        int i;
        static int j;
    endclass

    C c;
    assign c.i = 1;
    assign j = c.j;

    logic l;
    logic d[];
    assign l = d[2];

    logic q[$];
    logic [1:0] qp;
    assign qp = q[1:0];

    virtual I vif;
    assign vif.i = 1;

    wire bux;
    logic bix;
    assign (strong1, supply0) #(3,2,1) {bux, bix} = 2;

    function automatic blah(ref int i); endfunction
    assign bix = blah(j);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::DelayNotNumeric);
    CHECK(diags[1].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[2].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[3].code == diag::DynamicNotProcedural);
    CHECK(diags[4].code == diag::DynamicNotProcedural);
    CHECK(diags[5].code == diag::DynamicNotProcedural);
    CHECK(diags[6].code == diag::DynamicNotProcedural);
    CHECK(diags[7].code == diag::Delay3OnVar);
    CHECK(diags[8].code == diag::NonProceduralFuncArg);
    CHECK(diags[9].code == diag::MultipleContAssigns);
}

TEST_CASE("User defined nettypes") {
    auto tree1 = SyntaxTree::fromText(R"(
module m;
    import p::*;

    typedef logic[10:0] stuff;

    nettype foo bar;
    nettype stuff baz;

    // test that enum members get hoisted here
    nettype enum { SDF = 42 } blah;

    foo a = 1;
    bar b = 2;
    baz c = 3;
    blah d = SDF;
    bar e[5];

    baz #(3:2:1) f, g;
    baz #3.4 h = 1;

endmodule
)");
    auto tree2 = SyntaxTree::fromText(R"(
package p;
    nettype logic [3:0] foo;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    CHECK(root.lookupName<NetSymbol>("m.a").getType().toString() == "logic[3:0]");
    CHECK(root.lookupName<NetSymbol>("m.b").netType.name == "bar");
    CHECK(root.lookupName<NetSymbol>("m.b").getType().toString() == "logic[3:0]");
    CHECK(root.lookupName<NetSymbol>("m.c").getType().toString() == "m.stuff");
    CHECK(root.lookupName<NetSymbol>("m.e").getType().toString() == "logic[3:0]$[0:4]");
}

TEST_CASE("Invalid user defined nettypes") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef event t1[3];

    nettype event n1;
    nettype t1 n2;
    nettype struct { event e; } n3;
    nettype union { event e; } n4;

    nettype struct { real r; } n5;
    nettype union { real r; } n6;

    int foo[3];
    n6 #(foo) asdf;

    t1 #3 baz;

    // Assigning to a select or slice of a user-defined net
    // is not allowed.
    nettype struct { logic a; logic b; } n7;
    nettype logic[4:0] n8;

    n7 fizz;
    n8 buzz;
    assign fizz.b = 1;
    assign buzz[2:0] = 2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[1].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[2].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[3].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[4].code == diag::DelayNotNumeric);
    CHECK(diags[5].code == diag::VarDeclWithDelay);
    CHECK(diags[6].code == diag::UserDefPartialDriver);
    CHECK(diags[7].code == diag::UserDefPartialDriver);
}

TEST_CASE("Attributes") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam param = "str val";
    (* foo, bar = 1 *) (* baz = 1 + 2 * 3 *) wire foo, bar;

    (* blah *) n n1((* blah2 *) 0);

    (* blah3 = param *);

    function void func;
    endfunction

    int j;
    always_comb begin : block
        (* blah4 *) func (* blah5 *) ();
        j = 3 + (* blah6 *) 4;
    end

endmodule

module n((* asdf *) input foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto attrs = compilation.getAttributes(*root.lookupName("m.bar"));
    REQUIRE(attrs.size() == 3);
    CHECK(attrs[0]->getValue().integer() == SVInt(1));
    CHECK(attrs[1]->getValue().integer() == SVInt(1));
    CHECK(attrs[2]->getValue().integer() == SVInt(7));

    auto& n1 = root.lookupName<InstanceSymbol>("m.n1");
    attrs = compilation.getAttributes(n1);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah");

    auto ports = n1.body.membersOfType<PortSymbol>();
    REQUIRE(std::ranges::distance(ports) == 1);

    auto& fooPort = *ports.begin();
    attrs = compilation.getAttributes(fooPort);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "asdf");

    attrs = compilation.getAttributes(*n1.getPortConnection(fooPort));
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah2");

    auto& m = root.lookupName<InstanceSymbol>("m");
    attrs = compilation.getAttributes(*m.body.membersOfType<EmptyMemberSymbol>().begin());
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah3");
    CHECK(attrs[0]->getValue().convertToStr().str() == "str val");

    auto stmtList = m.body.membersOfType<ProceduralBlockSymbol>()
                        .begin()
                        ->getBody()
                        .as<BlockStatement>()
                        .body.as<StatementList>()
                        .list;
    REQUIRE(stmtList.size() == 2);

    attrs = compilation.getAttributes(*stmtList[0]);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah4");

    auto& call = stmtList[0]->as<ExpressionStatement>().expr.as<CallExpression>();
    attrs = compilation.getAttributes(call);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah5");

    auto& assign = stmtList[1]->as<ExpressionStatement>().expr.as<AssignmentExpression>();
    attrs = compilation.getAttributes(assign.right().as<BinaryExpression>());
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah6");
}

TEST_CASE("Attribute diagnostics") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    (* foo, foo = 2 *) wire foo;
    (* foo,, *) wire bar;
    (* foo = 1 + (* nested *) 3 *) wire baz;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::DuplicateAttribute);
    CHECK((it++)->code == diag::ExpectedIdentifier);
    CHECK((it++)->code == diag::MisplacedTrailingSeparator);
    CHECK((it++)->code == diag::AttributesNotAllowed);
    CHECK(it == diags.end());

    auto& root = compilation.getRoot();
    auto attrs = compilation.getAttributes(*root.lookupName("m.foo"));
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->getValue().integer() == SVInt(2));
}

TEST_CASE("Time units declarations") {
    auto tree = SyntaxTree::fromText(R"(
timeunit 10us;

module m;
    timeunit 10ns / 10ps;
    logic f;

    // Further decls ok as long as identical
    timeprecision 10ps;
    timeunit 10ns;
    timeunit 10ns / 10ps;
endmodule

module n;
endmodule

`timescale 100s / 10fs
module o;
endmodule

package p;
    timeprecision 1ps;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto ts = [](std::string_view str) { return TimeScale::fromString(str).value(); };

    auto getDefTS = [&](std::string_view name) {
        auto def = compilation.tryGetDefinition(name, compilation.getRoot()).definition;
        REQUIRE(def);
        return def->as<DefinitionSymbol>().timeScale;
    };

    CHECK(getDefTS("m") == ts("10ns/10ps"));
    CHECK(getDefTS("n") == ts("10us/1ns"));
    CHECK(getDefTS("o") == ts("100s/10fs"));
    CHECK(compilation.getPackage("p")->getTimeScale() == ts("100s/1ps"));
}

TEST_CASE("Time units error cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    timeunit;
endmodule

module n;
    logic f;
    timeunit 10ns;
    timeunit 100ns / 10ps;
endmodule

module o;
    timeunit 20ns;
endmodule

module p;
    timeunit 10ns / 100ns;
endmodule

module q;
    timeunit 1fs;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ExpectedTimeLiteral);
    CHECK((it++)->code == diag::TimeScaleFirstInScope);
    CHECK((it++)->code == diag::MismatchedTimeScales);
    CHECK((it++)->code == diag::InvalidTimeScaleSpecifier);
    CHECK((it++)->code == diag::InvalidTimeScalePrecision);
    CHECK((it++)->code == diag::InvalidInferredTimeScale);
    CHECK(it == diags.end());
}

TEST_CASE("Timescale missing on some elems") {
    auto tree = SyntaxTree::fromText(R"(
package p;
endpackage

module m;
endmodule

module top;
    timeunit 1ns;
    m m1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MissingTimeScale);
    CHECK(diags[1].code == diag::MissingTimeScale);
}

TEST_CASE("Port decl in ANSI module") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a);
    input b;
endmodule

module n;
    input c;
endmodule

module o(a, b);
    input a, b, c;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::PortDeclInANSIModule);
    CHECK(diags[1].code == diag::UnusedPortDecl);
    CHECK(diags[2].code == diag::UnusedPortDecl);
}

TEST_CASE("Module non-ansi port lookup locations") {
    auto tree = SyntaxTree::fromText(R"(
module m(mask, hbit);
   parameter outbits = 4;
   output reg [outbits-1:0] hbit;

   input [size-1:0] mask;
   parameter size = 16;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UsedBeforeDeclared);
}

TEST_CASE("always_comb") {
    auto tree = SyntaxTree::fromText(R"(
module module1
#(
    parameter int P1 = 5,
    parameter int P2 = 5
)
(
    input  logic [P1-1:0]   in1,
    input  logic [P2-1:0]   in2,
    input  logic [3:0]      in3,

    output logic [P1-1:0]   out1,
    output logic [P1-1:0]   out2,
    output logic [P1-1:0]   out3
);

    always_comb out1 = in1;

    always_comb begin
        out2 = in2;
        out3 = {1'b0, in3};
    end

    logic [7:0] arr1;

endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& alwaysComb = instance.body.memberAt<ProceduralBlockSymbol>(14);

    CHECK(alwaysComb.procedureKind == ProceduralBlockKind::AlwaysComb);

    const auto& variable = instance.body.memberAt<VariableSymbol>(16);
    CHECK(variable.getType().isIntegral());
    CHECK(variable.name == "arr1");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Implicit nets") {
    auto tree = SyntaxTree::fromText(R"(
module n(input logic a, output b);
endmodule

module m;
    n n1(asdf, asdf);
    n n2(.a(asdf), .b(foobar));

    assign foo = 1, bar = 0;

    reg i;
    assign tmp = i;

    int k = 5;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Implicit nets -- default_nettype none") {
    auto tree = SyntaxTree::fromText(R"(
module n(input logic a, output b);
endmodule

`default_nettype none
module m;
    n n1(asdf, asdf);

    assign foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Static initializer missing static keyword") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        int i = 4;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::StaticInitializerMustBeExplicit);
}

TEST_CASE("Automatic variable not allowed in module scope") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    automatic int i = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AutomaticNotAllowed);
}

TEST_CASE("Elaboration system tasks") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    m asdf();
endmodule

module m;
    $error;

    localparam int foo = 12;
    if (foo == 12)
        $info(4, 3.2, " %m:%l Hello world %0d!", foo + 2);
    else begin
        $warning("ASDFASDF");
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:7:5: error: $error encountered
    $error;
    ^
source:11:9: note: $info encountered:           43.200000 top.asdf.genblk1:work.m Hello world 14!
        $info(4, 3.2, " %m:%l Hello world %0d!", foo + 2);
        ^
)");
}

TEST_CASE("Elaboration task non-const args") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo = 4;
    $info("%d %d", 3, foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalNonConstVariable);
}

TEST_CASE("Escaped names in hierarchical path printing") {
    auto tree = SyntaxTree::fromText(R"(
module \module. ;
  if (1) begin : \foo.
    $info("\"%m\"");
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    auto result = "\n" + report(diagnostics);
    auto expected = R"(
source:4:5: note: $info encountered: \"\module. .\foo. \"
    $info("\"%m\"");
    ^
)";
    CHECK(result == expected);
}

TEST_CASE("Const variable must provide initializer") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    const int i;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstVarNoInitializer);
}

TEST_CASE("specparams") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    specparam s1 = 1:2:3;
    specparam s2 = 3.14;
    specparam [31:0] s3 = s1 + s2;

    logic [31:0] i = s3;
    localparam logic [31:0] j = s3;

    specify
        specparam s4 = 2:3:4;
        specparam s5 = j;
    endspecify

    int k = s4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::ArithOpMismatch);
    CHECK(diags[2].code == diag::SpecparamInConstant);
    CHECK(diags[3].code == diag::SpecifyBlockParam);
}

TEST_CASE("Net initializer in package") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    wire w = 1;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::PackageNetInit);
}

TEST_CASE("Clocking blocks") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    wire clk;
    int foo, a;
    clocking cb @clk;
        input a, b = foo;
        default input posedge #3;
        default output edge;
        inout foo;
        input #1step output #1step asdf = foo;
    endclocking

    clocking cb2 @clk; endclocking

    default clocking @clk; endclocking

    initial begin
        ##1 cb.foo <= 32;
        ##(foo + 1) cb.foo <= 32;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Clocking block errors") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    function f; endfunction

    wire clk, b;
    default clocking cb @clk;
        default input #1step output #0;
        default input posedge #3;
        default output edge;
        output a = b + 1;
        input f;
        input #b b;
        input #(-1) clk;
    endclocking

    default clocking cb;
    default clocking f;

    global clocking gb @clk; endclocking
    global clocking gb2 @clk; endclocking

    if (1) begin
        global clocking gb @clk; endclocking
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::MultipleDefaultInputSkew);
    CHECK(diags[1].code == diag::MultipleDefaultOutputSkew);
    CHECK(diags[2].code == diag::ExpressionNotAssignable);
    CHECK(diags[3].code == diag::InvalidClockingSignal);
    CHECK(diags[4].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[5].code == diag::ValueMustBePositive);
    CHECK(diags[6].code == diag::MultipleDefaultClocking);
    CHECK(diags[7].code == diag::NotAClockingBlock);
    CHECK(diags[8].code == diag::MultipleGlobalClocking);
    CHECK(diags[9].code == diag::GlobalClockingGenerate);
}

TEST_CASE("Multiple clocking blocks with ifaces") {
    auto tree = SyntaxTree::fromText(R"(
interface bus_A (input clk);
    logic [15:0] data;
    logic write;
    modport test (input clk, input data, output write);
    modport dut (output data, input write);
endinterface

interface bus_B (input clk);
    logic [8:1] cmd;
    logic enable;
    modport test (input clk, enable, output cmd);
    modport dut (output enable);
endinterface

program test( bus_A.test a, bus_B.test b );
    clocking cd1 @(posedge a.clk);
        input data = a.data;
        output write = a.write;
        inout state = top.state;
    endclocking

    clocking cd2 @(posedge b.clk);
        input #2 output #4ps cmd = b.cmd;
        input en = b.enable;
    endclocking
endprogram

module top;
    logic phi1, phi2;
    logic state;
    bus_A a (phi1);
    bus_B b (phi2);
    test main (a, b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Let declarations") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    logic clk, a, b;
    logic p, q, r;

    // let with formal arguments and default value on y
    let eq(x, y = b) = x == y;

    // without parameters, binds to a, b above
    let tmp = a && b;
    a1: assert property (@(posedge clk) eq(p,q));
    always_comb begin
        a2: assert (eq(r)); // use default for y
        a3: assert (tmp);
    end
endmodule : m1

module m2;
    logic x = 1'b1;
    logic a, b;
    let y = x;

    always_comb begin
        // y binds to preceding definition of x
        // in the declarative context of let
        automatic bit x = 1'b0;
        b = a | y;
    end
endmodule : m2

module m3;
    logic a, b;
    let x = a || b;
    sequence s;
        x ##1 b;
    endsequence : s
endmodule : m3

module m4;
    wire a, b;
    wire [2:0] c;
    wire [2:0] d;
    wire e;
    for (genvar i = 0; i < 3; i++) begin : L0
        if (i != 1) begin : L1
            let my_let(x) = !x || (b && c[i]);
            assign d[2 - i] = my_let(a); // OK
        end : L1
    end : L0
endmodule : m4

module m5(input clock);
    logic [15:0] a, b;
    logic c, d;
    typedef bit [15:0] bits;

    let ones_match(bits x, y) = x == y;
    let same(logic x, y) = x === y;
    always_comb a1: assert(ones_match(a, b));

    property toggles(bit x, y);
        same(x, y) |=> !same(x, y);
    endproperty

    a2: assert property (@(posedge clock) toggles(c, d));
endmodule : m5

module m6(input clock);
    logic a;
    let p1(x) = $past(x);
    let p2(x) = $past(x,,,@(posedge clock));
    let s(x) = $sampled(x);
    always_comb begin
        a1: assert(p1(a));
        a2: assert(p2(a));
        a3: assert(s(a));
    end
    a4: assert property(@(posedge clock) p1(a));
endmodule : m6

package pex_gen9_common_expressions;
    let valid_arb(request, valid, override) = |(request & valid) || override;
endpackage

module my_checker;
    import pex_gen9_common_expressions::*;
    logic a, b;
    wire [1:0] req;
    wire [1:0] vld;
    logic ovr;
    if (valid_arb(.request(req), .valid(vld), .override(ovr))) begin
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Let declaration errors") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    let foo(a, local b, input c, sequence d, int e) = a || b;
    let bar = bar;
    let baz = a + 1;
endmodule

module m;
    wire a, b;
    wire [2:0] c;
    wire [2:0] d;
    wire e;
    for (genvar i = 0; i < 3; i++) begin : L0
        if (i !=1) begin : L1
            let my_let(x) = !x || (b && c[i]);
            assign d[2 - i] = my_let(a); // OK
        end : L1
    end : L0
    assign e = L0[0].L1.my_let(a); // Illegal
endmodule : m
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::UnexpectedLetPortKeyword);
    CHECK(diags[1].code == diag::UnexpectedLetPortKeyword);
    CHECK(diags[2].code == diag::PropertyPortInLet);
    CHECK(diags[3].code == diag::RecursiveLet);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
    CHECK(diags[5].code == diag::LetHierarchical);
}

TEST_CASE("Hierarchical path strings") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    m m1 [4][6:1][3:4] ();
endmodule

module m;
    for (genvar i = 0; i < 10; i++) begin : asdf
        if (i == 1) begin
            int foo = 0;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot()
                    .lookupName<GenerateBlockArraySymbol>("top.m1[2][1][3].asdf")
                    .memberAt<GenerateBlockSymbol>(2)
                    .memberAt<GenerateBlockSymbol>(1)
                    .find<VariableSymbol>("foo");

    std::string path;
    foo.getHierarchicalPath(path);
    CHECK(path == "top.m1[2][1][3].asdf[1].genblk1.foo");
}

TEST_CASE("Hierarchical paths with unnamed generate arrays") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  genvar i;
  for (i = 0; i < 1; i = i + 1) begin
    logic a;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    std::string path;
    compilation.getRoot().visit(
        makeVisitor([&](auto& v, const VariableSymbol& sym) { sym.getHierarchicalPath(path); }));
    CHECK(path == "top.genblk1[0].a");
}

TEST_CASE("$static_assert elab task") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    m asdf();
endmodule

module m;
    localparam int foo = 12;

    struct packed { logic [4:1] a, b; } bar;

    $static_assert(foo < $bits(bar));
    $static_assert(foo & 0, "Stuff %0d", foo / 2);
    $static_assert(foo != 0, "Stuff Stuff %0d", foo / 2);
    $static_assert(bar > 0);

    initial begin
        $static_assert(foo > $bits(bar));
        $static_assert((foo < $bits(bar)));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:11:5: error: static assertion failed
    $static_assert(foo < $bits(bar));
    ^
source:11:24: note: comparison reduces to (12 < 8)
    $static_assert(foo < $bits(bar));
                   ~~~~^~~~~~~~~~~~
source:12:5: error: static assertion failed: Stuff 6
    $static_assert(foo & 0, "Stuff %0d", foo / 2);
    ^
source:14:20: error: reference to non-constant variable 'bar' is not allowed in a constant expression
    $static_assert(bar > 0);
                   ^~~
source:9:41: note: declared here
    struct packed { logic [4:1] a, b; } bar;
                                        ^
source:18:9: error: static assertion failed
        $static_assert((foo < $bits(bar)));
        ^
source:18:29: note: comparison reduces to (12 < 8)
        $static_assert((foo < $bits(bar)));
                        ~~~~^~~~~~~~~~~~
)");
}

TEST_CASE("static_assert ignore uninstantiated") {
    auto tree = SyntaxTree::fromText(R"(
module top;
endmodule

module m;
    $static_assert(0);
endmodule
)");

    CompilationOptions options;
    options.topModules.insert("top");
    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    CHECK(diagnostics.size() == 0);
}

TEST_CASE("$static_assert with let expression") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam i = 1;
    let isNegative(n) = n < 0;
    $static_assert(isNegative(i));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:5:5: error: static assertion failed
    $static_assert(isNegative(i));
    ^
source:4:27: note: comparison reduces to (1 < 0)
    let isNegative(n) = n < 0;
                        ~~^~~
)");
}

TEST_CASE("Interconnect nets") {
    auto tree = SyntaxTree::fromText(R"(
package p;
   typedef struct {
      bit a,b,c;
   } S;

   nettype S SNet;
endpackage:p

module top();
   interconnect bus;

   tb tb(bus);
   dut dut(bus);

   assign bus = 1;
   initial $display(bus);
endmodule

module tb import p::*; (output SNet so);
   assign so = '{0,1,1};
endmodule

module dut import p::*; (input SNet si);
   always @*
     $display("struct: %b%b%b", si.a, si.b, si.c);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InterconnectReference);
    CHECK(diags[1].code == diag::InterconnectReference);
}

TEST_CASE("always_comb / always_ff restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [2:0] a;
    int b = 1;
    int c;
    always_comb begin : boz
        a[0] = 1;
        a[1:0] = 2;
        b = 3;

        fork : baz
            automatic int d = 1;
        join_none
        c = 1;
    end

    wire clk;
    always_ff @(posedge clk) begin : baz
        a[1] <= 1;
    end

    always_latch begin : foo
        b = 4;
        fork join
    end

    always @* c = 3;

    int k;
    always_comb begin
        k = #1 3;
    end

    int l = 1;
    always_ff @(posedge clk) begin
        l <= 2;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ForkJoinAlwaysComb);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[3].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[4].code == diag::ForkJoinAlwaysComb);
    CHECK(diags[5].code == diag::TimingInFuncNotAllowed);
}

TEST_CASE("always_ff timing (pass)") {
    auto tree = SyntaxTree::fromText(R"(
module x;
reg a;
wire clk;
always_ff @(posedge clk)
  a <= #1 1'b0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 0);
}

TEST_CASE("always_ff timing (fail)") {
    auto tree = SyntaxTree::fromText(R"(
module x1;
reg a;
wire clk;
always_ff @(posedge clk)
  #1 a <= 1'b0;
endmodule
module x2;
reg a;
wire clk;
always_ff @(posedge clk)
  a = #1 1'b0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::BlockingInAlwaysFF);
    CHECK(diags[1].code == diag::BlockingInAlwaysFF);
}

TEST_CASE("always_comb drivers within nested functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int baz;

    function void f1(int bar);
      baz = bar;
    endfunction

    function void f2(int bar);
      f1(bar);
    endfunction

    always_comb f2(2);
    always_comb f2(3);

    int v;
    function void f3(int bar);
      v = bar;
    endfunction

    always_comb f3(4);

    int foo;
    task t;
      foo <= 1;
    endtask

    always_comb begin
      foo <= 2;
      t();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("always_comb timing inside assertion") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire b;
    always_comb begin
        assert property (@(posedge b) ((b) and b) ##0 b);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("User defined net examples") {
    auto tree = SyntaxTree::fromText(R"(
// user-defined data type T
typedef struct {
    real field1;
    bit field2;
} T;

// user-defined resolution function Tsum
function automatic T Tsum (input T driver[]);
    Tsum.field1 = 0.0;
    foreach (driver[i])
        Tsum.field1 += driver[i].field1;
endfunction

nettype T wT; // an unresolved nettype wT whose data type is T

// a nettype wTsum whose data type is T and
// resolution function is Tsum
nettype T wTsum with Tsum;

// user-defined data type TR
typedef real TR[5];

// an unresolved nettype wTR whose data type
// is an array of real
nettype TR wTR;

// declare another name nettypeid2 for nettype wTsum
nettype wTsum nettypeid2;

class Base #(parameter p = 1);
    typedef struct {
        real r;
        bit[p-1:0] data;
    } T;

    static function T Tsum (input T driver[]);
        Tsum.r = 0.0;
        Tsum.data = 0;
        foreach (driver[i])
            Tsum.data += driver[i].data;
        Tsum.r = $itor(Tsum.data);
    endfunction
endclass

typedef Base#(32) MyBaseT;
nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;

typedef Base#(64) MyBaseType;
nettype MyBaseType::T wideTsum with MyBaseType::Tsum;

module m;
    narrowTsum net1; // data is 32 bits wide
    wideTsum net2; // data is 64 bits wide

    var type(net1.data) d1;
    var type(net2.data) d2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("always_comb dup driver with initial block with language option") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[2];

    initial begin
        for (int i = 0; i < 2; i++)
            foo[i] = 0;
    end

    always_comb foo[1] = 1;
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowDupInitialDrivers;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("always_ff timing control restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    always_ff i <= 1;

    wire clk;
    int j;
    always_ff begin
        begin : a @(posedge clk) j <= 1; end
        begin : b @(negedge clk) j <= 0; end
        #3 j <= 2;
    end

endmodule

interface I;
    logic clk;
    modport foo (input clk);
endinterface

module n (I.foo i);
    always_ff @(posedge i.clk) begin end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::AlwaysFFEventControl);
    CHECK(diags[1].code == diag::AlwaysFFEventControl);
    CHECK(diags[2].code == diag::BlockingInAlwaysFF);
}

TEST_CASE("hierarchical driver errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int foo;
endinterface

module m;
    I i();

    n n1(i);
    n n2(i);
endmodule

module n(I i);
    always_comb i.foo = 1;
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::DisableInstanceCaching;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:14:17: error: variable 'foo' driven by always_comb procedure cannot be written to by any other process
    always_comb i.foo = 1;
                ^~~~~
note: from 'm.n2' and 'm.n1'
)");
}

TEST_CASE("lvalue driver assertion regression GH #551") {
    auto tree = SyntaxTree::fromText(R"(
module M #(parameter int W=1) (
    input  logic         clk,
    input  logic         rst,
    input  logic [W-1:0] d,
    output logic [W-1:0] o
);
endmodule

module M2 #(
    parameter int W = 2
) (
    input logic clk,
    input logic rst
);
    localparam int W_MAX = $clog2(W);

    logic [W_MAX:0] d, o;
    logic x_d, x_o;

    M m [W_MAX+1:0] (
        .clk (clk),
        .rst (rst),
        .d   ({x_d, d}),
        .o   ({x_o, o})
    );
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Specify path descriptions") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, [8:0] C, output b, Q);
    specify
        (a +*> b) = 1;

        (C[0] => Q) = 20;
        (C[1] => Q) = 10:14:20;

        // two expressions specify rise and fall delays
        specparam tPLH1 = 12, tPHL1 = 25;
        specparam tPLH2 = 12:16:22, tPHL2 = 16:22:25;
        (C[2] => Q) = ( tPLH1, tPHL1 ) ;
        (C[3] => Q) = ( tPLH2, tPHL2 ) ;
    endspecify
endmodule

module n(input [7:4] C, output Q);
    specify
        // three expressions specify rise, fall, and z transition delays
        specparam tPLH1 = 12, tPHL1 = 22, tPz1 = 34;
        specparam tPLH2 = 12:14:30, tPHL2 = 16:22:40, tPz2 = 22:30:34;
        (C[4] -=> (Q+:1)) = (tPLH1, tPHL1, tPz1);
        (C[5] => (Q-:1)) = (tPLH2, tPHL2, tPz2);

        // six expressions specify transitions to/from 0, 1, and z
        specparam t01 = 12, t10 = 16, t0z = 13,
                  tz1 = 10, t1z = 14, tz0 = 34 ;
        (C[6] => Q) = ( t01, t10, t0z, tz1, t1z, tz0) ;
        specparam T01 = 12:14:24, T10 = 16:18:20, T0z = 13:16:30 ;
        specparam Tz1 = 10:12:16, T1z = 14:23:36, Tz0 = 15:19:34 ;
        (C[7] => Q) = ( T01, T10, T0z, Tz1, T1z, Tz0) ;
    endspecify
endmodule

module o(input C, output Q);
    specify
        // twelve expressions specify all transition delays explicitly
        specparam t01=10, t10=12, t0z=14, tz1=15, t1z=29, tz0=36,
                  t0x=14, tx1=15, t1x=15, tx0=14, txz=20, tzx=30 ;
        (C => Q) = (t01, t10, t0z, tz1, t1z, tz0,
                    t0x, tx1, t1x, tx0, txz, tzx) ;
    endspecify
endmodule

module XORgate (a, b, out);
    input a, b;
    output out;

    xor x1 (out, a, b);

    specify
        specparam noninvrise = 1, noninvfall = 2;
        specparam invertrise = 3, invertfall = 4;
        if (a) (b => out) = (invertrise, invertfall);
        if (b) (a => out) = (invertrise, invertfall);
        if (~a)(b => out) = (noninvrise, noninvfall);
        if (~b)(a => out) = (noninvrise, noninvfall);
        ifnone (b => out) = (1, 0);
    endspecify
endmodule

module ALU (o1, i1, i2, opcode);
    input [7:0] i1, i2;
    input [2:1] opcode;
    output [7:0] o1;

    specify
        specparam s1 = 2;
        if (opcode == 2'b00) (i1,i2 *> o1) = (25.0, 25.0);
        if (opcode == 2'b01) (i1 => o1) = (5.6, 8.0);
        if (opcode == s1[1:0]) (i2 => o1) = (5.6, 8.0);
        (opcode *> o1) = (6.1, 6.5);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Specify path errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    int i;
    modport m(input i);
endinterface

int k;

module m(input [4:0] a, output [4:0] b, z[6], output [5:0] l, I.m foo, I bar);
    localparam int c = 1;
    struct packed { logic a; logic b; } d;
    logic [1:0][1:0] e;
    real f;
    int g;
    event ev;

    specify
        (a +*> c) = 1;
        (a[0+:1] *> b[0]) = 1;
        (d.a *> b) = 1;
        (e[0][1] *> b) = 1;
        (f *> b) = 1;
        (g *> b) = 1;
        (a *> foo.i) = 1;
        (a *> bar.i) = 1;
        (a *> k) = 1;
        (a => l) = 1;
        (a => z[0]) = ev;

        if (k < 2) (a => z[1]) = 1;
        if (1 < 2) (a => z[2]) = 1;
        if (byte'(g) == 1) (a => z[3]) = 1;
        if (+g == 1) (a => z[4]) = 1;
        if (g inside { 1, 2 }) (a => z[5]) = 1;

        (b => a) = 1;
    endspecify
endmodule

module n;
    I foo(), bar();
    logic [4:0] a,b,z[6];
    logic [5:0] l;
    m m1(.*);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 18);
    CHECK(diags[0].code == diag::InvalidSpecifyDest);
    CHECK(diags[1].code == diag::SpecifyBlockParam);
    CHECK(diags[2].code == diag::InvalidSpecifyPath);
    CHECK(diags[3].code == diag::SpecifyPathMultiDim);
    CHECK(diags[4].code == diag::InvalidSpecifyType);
    CHECK(diags[5].code == diag::InvalidSpecifySource);
    CHECK(diags[6].code == diag::InvalidSpecifyDest);
    CHECK(diags[7].code == diag::InvalidSpecifyPath);
    CHECK(diags[8].code == diag::ParallelPathWidth);
    CHECK(diags[9].code == diag::DelayNotNumeric);
    CHECK(diags[10].code == diag::SpecifyPathBadReference);
    CHECK(diags[11].code == diag::SpecifyPathConditionExpr);
    CHECK(diags[12].code == diag::SpecifyPathConditionExpr);
    CHECK(diags[13].code == diag::SpecifyPathConditionExpr);
    CHECK(diags[14].code == diag::SpecifyPathConditionExpr);
    CHECK(diags[15].code == diag::SpecifyPathConditionExpr);
    CHECK(diags[16].code == diag::InvalidSpecifySource);
    CHECK(diags[17].code == diag::InvalidSpecifyDest);
}

TEST_CASE("Pathpulse specparams") {
    auto tree = SyntaxTree::fromText(R"(
module m(input foo, output bar);
    typedef int blah;
    specify
        specparam PATHPULSE$ = (1, 2);
        specparam l = PATHPULSE$;
        specparam PATHPULSE$foo$bar = (1, 2);
        specparam PATHPULSE$foo$baz = (1, 2);
        specparam PATHPULSE$foo$foo = (1, 2);
        specparam PATHPULSE$foo$blah = (1, 2);
        specparam PATHPULSE$asdf = (1, 2);
        specparam PATHPULSE$foo$ = (1, 2);
        specparam PATHPULSE$$bar = (1, 2);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::PathPulseInExpr);
    CHECK(diags[1].code == diag::TypoIdentifier);
    CHECK(diags[2].code == diag::InvalidSpecifyDest);
    CHECK(diags[3].code == diag::InvalidSpecifyDest);
    CHECK(diags[4].code == diag::PathPulseInvalidPathName);
    CHECK(diags[5].code == diag::PathPulseInvalidPathName);
    CHECK(diags[6].code == diag::PathPulseInvalidPathName);
}

TEST_CASE("Specify pulsestyle directives") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, output b);
    specify
        pulsestyle_onevent a, b, b;
        pulsestyle_ondetect b;
        showcancelled b;
        noshowcancelled b, b;
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidSpecifyDest);
}

TEST_CASE("System timing checks") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, clk, data, output b);
    reg notify;
    wire bar;
    wire [1:0] w;

    specify
        specparam tSU = 1, tHLD = 3:4:5;
        $setup(posedge clk, data, 42);
        $hold(posedge clk, data, 42, );
        $setuphold(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, dclk, ddata);
        $recovery(posedge clk, data, 42);
        $removal(posedge clk, data, 42, );
        $recrem(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, dclk);
        $recrem(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, w[0], ddata);
        $skew(posedge clk, data, 42);
        $timeskew(posedge clk, negedge data, 42, , 1, 0:1:0);
        $fullskew(posedge clk, negedge data, 42, 32, , 1, 0:1:0);
        $period(edge [01, x1, 1Z] clk, 42, notify);
        $width(posedge clk, 42, 52);
        $nochange(posedge clk, negedge data, -1, -2);
    endspecify

    wire x = dclk;
    wire y = ~ddata;
endmodule

`default_nettype none
module n(input wire clk, data, output reg b);
    logic dclk, ddata;
    specify
        $recrem(posedge clk, data, 1, 2, , , , dclk, );
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("System timing check errors") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, output b);
    reg notify;
    enum { ABC } abc;
    int d[];

    specify
        $foobar(1, 2, 3);
        $setup(posedge a);
        $setup(posedge a, negedge a, 123, notify, 123);
        $setup(posedge a, , 123, notify);
        $setup(posedge a, negedge a, negedge a, notify);
        $setup(posedge a, negedge a, 1:2:3, notify);
        $setup(posedge a, negedge a, notify, notify);
        $setup(posedge a, negedge a, 1, notify[0]);
        $setup(posedge a, negedge a, 1, ABC);
        $setup(posedge a &&& d, negedge a, 1);
        $setup(edge [1xx] a &&& notify, negedge a, 1);
        $setup(posedge a, a, -12.14);
        $width(a, 1);
        $nochange(edge [1x] a, a, 1, 2);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 13);
    CHECK(diags[0].code == diag::UnknownSystemTimingCheck);
    CHECK(diags[1].code == diag::TooFewArguments);
    CHECK(diags[2].code == diag::TooManyArguments);
    CHECK(diags[3].code == diag::EmptyArgNotAllowed);
    CHECK(diags[4].code == diag::TimingCheckEventNotAllowed);
    CHECK(diags[5].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[6].code == diag::InvalidTimingCheckNotifierArg);
    CHECK(diags[7].code == diag::BadAssignment);
    CHECK(diags[8].code == diag::NotBooleanConvertible);
    CHECK(diags[9].code == diag::InvalidEdgeDescriptor);
    CHECK(diags[10].code == diag::NegativeTimingLimit);
    CHECK(diags[11].code == diag::TimingCheckEventEdgeRequired);
    CHECK(diags[12].code == diag::NoChangeEdgeRequired);
}

TEST_CASE("System timing check implicit nets") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    specify
        $setup(a &&& b, c, 1);
        $setuphold(a, b, 1, 2, , d, e);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Specify path dup warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, clk, reset, [3:0] c, output b, out, [3:0] q, d);
    logic data;
    specify
        (a => b) = 1;
    endspecify

    specify
        (a => b) = 1;
        (c[1:0], c[2], c[3], c[0] *> d[1:0]) = 1;
        (c *> d, d) = 1;

        // These are not dups
        (posedge clk => (q[0] : data)) = (10, 5);
        (negedge clk => (q[0] : data)) = (20, 12);

        // Also not dups
        if (reset)
            (posedge clk => (q[1] : data)) = (15, 8);
        if (!reset)
            (posedge clk => (q[1] : data)) = (6, 2);
        if (reset && clk)
            (posedge clk => (q[1] : data)) = (15, 8);

        // This is a dup because of the select range
        if (~reset && ~clk)
            (negedge clk *> (q[2:1] : data)) = (6, 2);

        if (a) (a => out) = (2,2);
        if (b) (a => out) = (2,2);
        ifnone (a => out) = (1,1);
        ifnone (a => out) = (1,1);
        (a => out) = (1,1);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::DupTimingPath);
    CHECK(diags[1].code == diag::DupTimingPath);
    CHECK(diags[2].code == diag::DupTimingPath);
    CHECK(diags[3].code == diag::DupTimingPath);
    CHECK(diags[4].code == diag::DupTimingPath);
    CHECK(diags[5].code == diag::DupTimingPath);
}

TEST_CASE("Invalid pulse style warning") {
    auto tree = SyntaxTree::fromText(R"(
module m(input a, output b, c);
    specify
        (a => b) = 1;
        pulsestyle_ondetect b, c;
        (a => c) = 1;
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidPulseStyle);
}

TEST_CASE("Charge and drive strength API access") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    assign (supply1, weak0) foo = 1;
    pullup (strong1) p1 (a);
    trireg (small) b;
    wire (highz0, pull1) c = 0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& m = compilation.getRoot().topInstances[0]->body;

    auto ds = m.membersOfType<ContinuousAssignSymbol>().begin()->getDriveStrength();
    CHECK(ds.first == DriveStrength::Weak);
    CHECK(ds.second == DriveStrength::Supply);

    ds = m.find<PrimitiveInstanceSymbol>("p1").getDriveStrength();
    CHECK(!ds.first);
    CHECK(ds.second == DriveStrength::Strong);

    ds = m.find<NetSymbol>("c").getDriveStrength();
    CHECK(ds.first == DriveStrength::HighZ);
    CHECK(ds.second == DriveStrength::Pull);

    auto cs = m.find<NetSymbol>("b").getChargeStrength();
    CHECK(cs == ChargeStrength::Small);
}

TEST_CASE("Net alias directives") {
    auto tree = SyntaxTree::fromText(R"(
module byte_swap (inout wire [31:0] A, inout wire [31:0] B);
    alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;
endmodule

module byte_rip (inout wire [31:0] W, inout wire [7:0] LSB, MSB);
    alias W[7:0] = LSB;
    alias W[31:24] = MSB;
endmodule

module overlap1(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
    alias bus16[11:0] = low12;
    alias bus16[15:4] = high12;
endmodule

module overlap2(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
    alias bus16 = {high12, low12[3:0]};
    alias high12[7:0] = low12[11:4];
endmodule

module overlap3(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
    alias low12 = bus16[11:0];
    alias high12 = bus16[15:4];
endmodule

module overlap4(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
    alias {high12, low12[3:0]} = bus16;
    alias low12[11:4] = high12[7:0];
endmodule

module lib1_dff(input logic Reset, Clk, Data, Q, Q_Bar);
endmodule

module my_dff(rst, clk, d, q, q_bar);
    input rst, clk, d;
    output q, q_bar;
    alias rst = Reset = reset = RST;
    alias clk = Clk = clock = CLK;
    alias d = Data = data = D;
    alias q = Q;
    alias Q_ = q_bar = Q_Bar = qbar;
    lib1_dff my_dff (.*);
endmodule

module m;
    wire [1:0] a, b, c;
    alias a = b[1:0];
    alias c = b[1:0];
endmodule

module m1(input wire [15:0] a, input wire [1:0] b);
    alias {a[0], a[1]} = b[1:0];
endmodule

module m2(input wire [15:0] a, input wire [1:0] b);
    alias {a[0], a[1]} = b;
endmodule

module m3(input wire [15:0] a, input wire [1:0] b);
    alias a[1] = b[0];
    alias a[0] = b[1];
endmodule

module m4(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
    alias {a[1], c[0]} = {d[0], b[1]};
endmodule

module m5(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
    alias {b, b} = {c, d};
endmodule

module m6(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
   alias {b, e}  = {c, d};
endmodule

module m7(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
   alias b = d;
   alias {b, e[0]}  = {c, d[0]};
   alias e[1] = d[1];
endmodule

module m8(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
   alias {b, e[0]}  = {c, d[0]};
   alias e[1] = d[2];
endmodule

module m9(input wire [15:0] a, input wire [15:0] b, input wire [14:0] c, input wire [15:0] d, input wire [2:0] e);
  alias b[13:0] = d[13:0];
  alias b  = {c, d[14]};
endmodule

module m10(input wire [15:0] a, input wire [1:0] b);
  alias a[1] = b[0];
  alias a[0] = a[1];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Net alias errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire [1:0] a;
    wire [3:1] b;
    logic [1:0] c;
    wor [1:0] d;

    alias a = b;
    alias a = 1;
    alias a = c = m.c = d;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::NetAliasWidthMismatch);
    CHECK(diags[1].code == diag::ExpressionNotAssignable);
    CHECK(diags[2].code == diag::NetAliasNotANet);
    CHECK(diags[3].code == diag::NetAliasHierarchical);
    CHECK(diags[4].code == diag::NetAliasCommonNetType);
}

TEST_CASE("Net alias overlap") {
    auto tree = SyntaxTree::fromText(R"(
module overlap(inout wire [15:0] bus16, inout wire [11:0] low12, high12, inout wire [32:0] c, inout wire [16:0] b, inout wire [32:0] b2);
    alias bus16 = {{high12[4:0], high12[6:0]}, bus16[3:0]} = {bus16[15:12], high12};
    alias low12[0:0] = a;
    alias low12 = {low12} = {low12};
    alias a = a;
    alias b[2:0] = {c[2:0]};
    alias b1 = {c[1:1]};
    alias b2 = c;
    alias bus16 = {high12[11:8], low12};
    alias bus16 = {high12, low12[3:0]};
    alias bus16 = {high12, bus16[3:0]} = {bus16[15:12], low12};
    module overlapnested(inout wire [15:0] bus15);
        alias bus15 = bus16;
        alias bus15 = bus16;
    endmodule
    overlapnested ov(bus16);
endmodule

module m1(input wire [15:0] a, input wire [1:0] b);
    alias {a[0], a[1]} = b[1:0];
    alias {a[0], a[1]} = b;
    alias a[1] = b[0];
    alias a[0] = b[1];
endmodule

module m2(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
    alias {b, b} = {c, d};
   alias {b, e}  = {c, d};
endmodule

module m3(input wire [15:0] a, input wire [2:0] b, input wire [2:0] c, input wire [2:0] d, input wire [2:0] e);
   alias b = d;
   alias {b, e[0]}  = {c, d[0]};
   alias e[1] = d[1];
   alias {b, e[0]}  = {c, d[0]};
   alias e[1] = d[2];
endmodule

module m10(input wire [15:0] a, input wire [15:0] b, input wire [14:0] c, input wire [15:0] d, input wire [2:0] e);
  alias b[14:0] = d[14:0];
  alias b  = {c, d[14]};
endmodule

module m11(input wire [15:0] a, input wire [1:0] b);
  alias a[1] = b[0];
  alias a[0] = b[0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 22);
    CHECK(diags[0].code == diag::MultipleNetAlias);
    CHECK(diags[1].code == diag::NetAliasSelf);
    CHECK(diags[2].code == diag::NetAliasSelf);
    CHECK(diags[3].code == diag::MultipleNetAlias);
    CHECK(diags[4].code == diag::MultipleNetAlias);
    CHECK(diags[5].code == diag::NetAliasSelf);
    CHECK(diags[6].code == diag::NetAliasSelf);
    CHECK(diags[7].code == diag::NetAliasSelf);
    CHECK(diags[8].code == diag::MultipleNetAlias);
    CHECK(diags[9].code == diag::MultipleNetAlias);
    CHECK(diags[10].code == diag::NetAliasSelf);
    CHECK(diags[11].code == diag::MultipleNetAlias);
    CHECK(diags[12].code == diag::MultipleNetAlias);
    CHECK(diags[13].code == diag::MultipleNetAlias);
    CHECK(diags[14].code == diag::MultipleNetAlias);
    CHECK(diags[15].code == diag::MultipleNetAlias);
    CHECK(diags[16].code == diag::MultipleNetAlias);
    CHECK(diags[17].code == diag::MultipleNetAlias);
    CHECK(diags[18].code == diag::MultipleNetAlias);
    CHECK(diags[19].code == diag::MultipleNetAlias);
    CHECK(diags[20].code == diag::MultipleNetAlias);
    CHECK(diags[21].code == diag::MultipleNetAlias);
}

TEST_CASE("Action block parsing regress GH #911") {
    auto tree = SyntaxTree::fromText(R"(
module M #(
    A = 1
);
logic clk, rst;

property myprop(k);
   @(posedge clk) disable iff(rst !== 0) k > 0;
endproperty

genvar k;
for (k=1; k < 4; k++) begin: m
    if (A)
        label1: assert property(myprop(k));
    else
        label2: assert property(myprop(k));

    if (A)
        label3: assert property(myprop(k))
                else $error("assert failed");
    else
        label4: assert property(myprop(k));

    if (A) begin
        label5: assert property(myprop(k));
    end else
        label6: assert property(myprop(k));
end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Function result chaining is allowed") {
    auto tree = SyntaxTree::fromText(R"(
class Node;
    typedef bit [15:10] value_t;
    protected Node m_next;
    protected value_t m_val;

    function new(value_t v); m_val = v; endfunction
    function void set_next(Node n); m_next = n; endfunction
    function Node get_next(); return m_next; endfunction
    function value_t get_val(); return m_val; endfunction
endclass

function Node get_first_node();
    Node n1, n2;
    n1 = new(6'h00);
    n2 = new(6'h3F);
    n1.set_next(n2);
    return n1;
endfunction

module m;
    initial begin
        bit [3:0] my_bits;
        my_bits = get_first_node().get_next().get_val()[13:10];
    end
endmodule

class A;
    real member=1;
endclass

module top;
    A a;
    function A F;
        int member;
        a = new();
        return a;
    endfunction

    initial begin
        $display(F.member);
        $display(F().member);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface comparison") {
    auto tree = SyntaxTree::fromText(R"(
interface PBus1 #(parameter WIDTH=8);
        logic req, grant;
        logic [WIDTH-1:0] addr, data;
        modport phy(input addr, ref data);
endinterface

module top;
        PBus1 #(16) p16();
        virtual PBus1 #(16) v16;

        initial begin
                if (p16 == v16) begin end
                if (v16 == p16) begin end
                if (v16 == v16) begin end
        end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Instance comparison") {
    auto tree = SyntaxTree::fromText(R"(
interface PBus1 #(parameter WIDTH=8);
        logic req, grant;
        logic [WIDTH-1:0] addr, data;
        modport phy(input addr, ref data);
endinterface

module top;
        PBus1 #(16) p16();
        initial begin
                if (p16 == p16) begin end
        end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CannotCompareTwoInstances);
}

TEST_CASE("Virtual interfaces of different types comparison") {
    auto tree = SyntaxTree::fromText(R"(
interface PBus1 #(parameter WIDTH=8);
        logic req, grant;
        logic [WIDTH-1:0] addr, data;
        modport phy(input addr, ref data);
endinterface

interface PBus2 #(parameter WIDTH=8);
        logic req, grant;
        logic [WIDTH-1:0] addr, data;
        modport phy(input addr, ref data);
endinterface

module top;
        virtual PBus1 #(16) v16;
        virtual PBus2 #(16) v26;
        PBus1 #(16) p16();
        initial begin
                if (p16 == v26) begin end
                if (v16 == v26) begin end
        end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::BadBinaryExpression);
    CHECK(diags[1].code == diag::BadBinaryExpression);
}

TEST_CASE("Package import / export from self") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int i;

    function foo;
        import p::i;
        import p::*;
    endfunction

    export p::i;
    export p::*;
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::PackageImportSelf);
    CHECK(diags[1].code == diag::PackageImportSelf);
    CHECK(diags[2].code == diag::PackageExportSelf);
    CHECK(diags[3].code == diag::Redefinition);
    CHECK(diags[4].code == diag::PackageExportSelf);
}

TEST_CASE("DPI task import has correct return type") {
    auto tree = SyntaxTree::fromText(R"(
module t;
    task task1;
    endtask

    import "DPI-C" context task dpi_init;

    initial begin
        dpi_init;
        task1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Timing check arg restriction regress -- GH #1084") {
    auto tree = SyntaxTree::fromText(R"(
module clk_gate_and(
        input  logic clk_in,
        input  logic clk_en,
        output logic clk_out
    );

    specify
        specparam setup = 10;
        specparam hold = 10;

        $setup(posedge clk_in, clk_en, setup);
        $hold(posedge clk_in, clk_en, hold);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Net alias infinite loop regress") {
    auto tree = SyntaxTree::fromText(R"(
alias;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}
