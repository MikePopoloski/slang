#include "Test.h"
#include <nlohmann/json.hpp>

#include "slang/binding/OperatorExpressions.h"
#include "slang/symbols/AttributeSymbol.h"

TEST_CASE("Nets") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    wire logic f = 1;
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

    logic bar;
    assign bar = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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
    CHECK(root.lookupName<NetSymbol>("m.b").netType.getAliasTarget()->name == "foo");
    CHECK(root.lookupName<NetSymbol>("m.b").getType().toString() == "logic[3:0]");
    CHECK(root.lookupName<NetSymbol>("m.c").getType().toString() == "logic[10:0]");
    CHECK(root.lookupName<NetSymbol>("m.e").getType().toString() == "logic[3:0]$[0:4]");
}

TEST_CASE("JSON dump") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    modport m(input f);
endinterface

package p1;
    parameter int BLAH = 1;
endpackage

module Top;
    wire foo;
    assign foo = 1;

    (* foo, bar = 1 *) I array [3] ();

    always_comb begin
    end

    if (1) begin
    end

    for (genvar i = 0; i < 10; i++) begin
    end

    import p1::BLAH;

    import p1::*;

    logic f;
    I stuff();
    Child child(.i(stuff), .f);

    function logic func(logic bar);
    endfunction

endmodule

module Child(I.m i, input logic f = 1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    // This basic test just makes sure that JSON dumping doesn't crash.
    json output = compilation.getRoot();
    output.dump();
}

TEST_CASE("Attributes") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam param = "str val";
    (* foo, bar = 1 *) (* baz = 1 + 2 * 3 *) wire foo, bar;

    (* blah *) n n1((* blah2 *) 0);

    // TODO: (* blah3 = param *);
    (* blah3 *);

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

    auto ports = n1.membersOfType<PortSymbol>();
    REQUIRE(ports.size() == 1);

    auto& fooPort = *ports.begin();
    attrs = compilation.getAttributes(fooPort);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "asdf");

    attrs = fooPort.getConnectionAttributes();
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah2");

    auto& m = root.lookupName<InstanceSymbol>("m");
    attrs = compilation.getAttributes(*m.membersOfType<EmptyMemberSymbol>().begin());
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah3");
    
    // TODO:
    //CHECK(attrs[0]->getValue().convertToStr().str() == "str val");

    auto& block = root.lookupName<StatementBlockSymbol>("m.block");
    auto stmtList = block.getBody().as<StatementList>().list;
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

    CHECK(compilation.getDefinition("m")->getTimeScale() == TimeScale("10ns", "10ps"));
    CHECK(compilation.getDefinition("n")->getTimeScale() == TimeScale("10us", "1ns"));
    CHECK(compilation.getDefinition("o")->getTimeScale() == TimeScale("100s", "10fs"));
    CHECK(compilation.getPackage("p")->getTimeScale() == TimeScale("100s", "1ps"));
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
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::ExpectedTimeLiteral);
    CHECK((it++)->code == diag::TimeScaleFirstInScope);
    CHECK((it++)->code == diag::MismatchedTimeScales);
    CHECK((it++)->code == diag::InvalidTimeScaleSpecifier);
    CHECK(it == diags.end());
}

TEST_CASE("Port decl in ANSI module") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a);
    input b;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    auto it = diags.begin();
    CHECK((it++)->code == diag::PortDeclInANSIModule);
    CHECK(it == diags.end());
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

TEST_CASE("Functions -- body params") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo;
        input i;
        output logic [1:0] baz;
        baz = i;
        foo = i;
    endfunction

    logic [1:0] b;
    logic j;
    initial j = foo(1, b);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Functions -- mixed param types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo(int j, int b);
        input i;
        output logic [1:0] baz;
        baz = i;
        foo = i;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MixingSubroutinePortKinds);
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