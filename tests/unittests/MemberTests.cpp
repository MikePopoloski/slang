#include "Test.h"

#include "slang/binding/OperatorExpressions.h"
#include "slang/compilation/Definition.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/text/Json.h"
#include "slang/types/NetType.h"

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
    CHECK(root.lookupName<NetSymbol>("m.b").netType.getAliasTarget()->name == "foo");
    CHECK(root.lookupName<NetSymbol>("m.b").getType().toString() == "logic[3:0]");
    CHECK(root.lookupName<NetSymbol>("m.c").getType().toString() == "logic[10:0]");
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
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[1].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[2].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[3].code == diag::InvalidUserDefinedNetType);
    CHECK(diags[4].code == diag::DelayNotNumeric);
    CHECK(diags[5].code == diag::VarDeclWithDelay);
}

TEST_CASE("JSON dump") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic f;
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
    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(compilation, writer);
    serializer.serialize(compilation.getRoot());
    writer.view();
}

TEST_CASE("JSON dump -- types and values") {
    auto tree = SyntaxTree::fromText(R"(
module test_enum;
    typedef enum logic {
        STATE_0 = 0,
        STATE_1 = 1
    } STATE;

    STATE a = STATE_0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(compilation, writer);
    serializer.setIncludeAddresses(false);
    serializer.serialize(compilation.getRoot());

    std::string result = "\n"s + std::string(writer.view());
    CHECK(result == R"(
{
  "name": "$root",
  "kind": "Root",
  "members": [
    {
      "name": "",
      "kind": "CompilationUnit"
    },
    {
      "name": "test_enum",
      "kind": "Instance",
      "body": {
        "name": "test_enum",
        "kind": "InstanceBody",
        "members": [
          {
            "name": "STATE_0",
            "kind": "TransparentMember"
          },
          {
            "name": "STATE_1",
            "kind": "TransparentMember"
          },
          {
            "name": "STATE",
            "kind": "TypeAlias",
            "target": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.e$1"
          },
          {
            "name": "a",
            "kind": "Variable",
            "type": {
              "name": "STATE",
              "kind": "TypeAlias",
              "target": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.e$1"
            },
            "initializer": {
              "kind": "NamedValue",
              "type": {
                "name": "STATE",
                "kind": "TypeAlias",
                "target": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.e$1"
              },
              "symbol": "STATE_0",
              "constant": "1'b0"
            },
            "lifetime": "Static",
            "isConstant": false,
            "isCompilerGenerated": false
          }
        ],
        "definition": "test_enum"
      }
    }
  ]
})");
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
    REQUIRE(ports.size() == 1);

    auto& fooPort = *ports.begin();
    attrs = compilation.getAttributes(fooPort);
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "asdf");

    attrs = n1.getPortConnection(fooPort)->attributes;
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah2");

    auto& m = root.lookupName<InstanceSymbol>("m");
    attrs = compilation.getAttributes(*m.body.membersOfType<EmptyMemberSymbol>().begin());
    REQUIRE(attrs.size() == 1);
    CHECK(attrs[0]->name == "blah3");
    CHECK(attrs[0]->getValue().convertToStr().str() == "str val");

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

    CHECK(compilation.getDefinition("m")->timeScale == TimeScale("10ns", "10ps"));
    CHECK(compilation.getDefinition("n")->timeScale == TimeScale("10us", "1ns"));
    CHECK(compilation.getDefinition("o")->timeScale == TimeScale("100s", "10fs"));
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

TEST_CASE("Functions -- body params") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo;
        input i;
        output logic [1:0] baz;
        const ref int asdf;
        logic [$bits(baz) - 2:0] i;
        baz[0] = i;
        foo = i;
    endfunction

    logic [1:0] b;
    logic j;
    int q;
    initial j = foo(1, b, q);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Functions -- body params -- port merging") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef logic[31:0] foo_t;
    function foo;
        input unsigned a;
        int a;
        input signed b;
        foo_t b[3];
        ref c[1:3][4:2];
        int c[1:3][1:1];
        input d[1:2];
        int d;
        input e[1:2];
        int e[1:2][3:4];
        int e;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::SignednessNoEffect);
    CHECK(diags[1].code == diag::SignednessNoEffect);
    CHECK(diags[2].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[3].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[4].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[5].code == diag::RedefinitionDifferentType);
}

TEST_CASE("Functions -- mixed param types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo(int j, int b);
        input i;
        output logic [1:0] baz;
        baz = 2'(i);
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

TEST_CASE("Various subroutine arg styles") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    task read(int j = 0, int k, int data = 1); endtask
    initial begin
        read(,5);
        read(2,5);
        read(,5,);
        read(,5,7);
        read(1,5,2);
    end

    function void fun(int j = 1, string s = "no"); endfunction
    initial begin
        fun(.j(2), .s("yes"));
        fun(.s("yes"));
        fun(, "yes");
        fun(.j(2));
        fun(.s("yes"), .j(2));
        fun(.s(), .j());
        fun(2);
        fun();
        fun(2, .s("yes"));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Various subroutine arg errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function void fun(int j, string s = "no"); endfunction
    initial begin
        fun(.j(0), .j(1));
        fun(.j(0), "yes");
        fun(,);
        fun(.j(), .s());
    end

    function void fun2(int j, string s); endfunction
    initial begin
        fun2(1);
        fun2(.j(1));
        fun2(1, "no", 2);
        fun2(1, .s("no"), .foo(3));
        fun2(1, "no", .j(1));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::DuplicateArgAssignment);
    CHECK(diags[1].code == diag::MixingOrderedAndNamedArgs);
    CHECK(diags[2].code == diag::ArgCannotBeEmpty);
    CHECK(diags[3].code == diag::ArgCannotBeEmpty);
    CHECK(diags[4].code == diag::TooFewArguments);
    CHECK(diags[5].code == diag::UnconnectedArg);
    CHECK(diags[6].code == diag::TooManyArguments);
    CHECK(diags[7].code == diag::ArgDoesNotExist);
    CHECK(diags[8].code == diag::DuplicateArgAssignment);
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

TEST_CASE("Function declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    function static logic [15:0] foo(a, int b, output logic [15:0] u, v, inout w);
        return 16'(a + b);
    endfunction
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& foo = instance.body.memberAt<SubroutineSymbol>(0);
    CHECK(foo.subroutineKind == SubroutineKind::Function);
    CHECK(foo.defaultLifetime == VariableLifetime::Static);
    CHECK(foo.getReturnType().getBitWidth() == 16);
    CHECK(foo.name == "foo");

    auto args = foo.getArguments();
    REQUIRE(args.size() == 5);
    CHECK(args[0]->getType().getBitWidth() == 1);
    CHECK(args[0]->direction == ArgumentDirection::In);
    CHECK(args[1]->getType().getBitWidth() == 32);
    CHECK(args[1]->direction == ArgumentDirection::In);
    CHECK(args[2]->getType().getBitWidth() == 16);
    CHECK(args[2]->direction == ArgumentDirection::Out);
    CHECK(args[3]->getType().getBitWidth() == 16);
    CHECK(args[3]->direction == ArgumentDirection::Out);
    CHECK(args[4]->getType().getBitWidth() == 1);
    CHECK(args[4]->direction == ArgumentDirection::InOut);

    const auto& returnStmt = foo.getBody().as<ReturnStatement>();
    REQUIRE(returnStmt.kind == StatementKind::Return);
    CHECK(!returnStmt.expr->bad());
    CHECK(returnStmt.expr->type->getBitWidth() == 16);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Gates") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    pullup (supply0, pull1) (1);
    cmos #3 asdf [3:0][4][5] (1, 2, 3), blah (4, 5), (5, 6);
    rtranif1 (1), asdf2(2);
    pmos #6 (a, b, c);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Implicit nets") {
    auto tree = SyntaxTree::fromText(R"(
module n(input logic a, output b);
endmodule

module m;
    n n1(asdf, asdf);
    n n2(.a(asdf), .b(foobar));

    assign foo = 1, bar = 2;
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

TEST_CASE("Implicit param with unpacked dimensions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter foo[3] = '{1,2,3};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnpackedArrayParamType);
}

TEST_CASE("Implicit param types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter [9:1] a = 9'b0;
    parameter b = '1;
    parameter c = 3.4;
    parameter signed d = 2'b10;
    parameter signed e = 3.4;
    parameter unsigned f = 3.4;
    parameter signed [3:5] g = 3.4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

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
module m;
    $error;

    localparam int foo = 12;
    if (foo == 12)
        $info(4, 3.2, "Hello world %d!", foo + 2);
    else begin
        $warning("ASDFASDF");
    end
        
endmodule
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:3:5: error: $error encountered
    $error;
    ^
source:7:9: note: $info encountered:           43.200000Hello world          14!
        $info(4, 3.2, "Hello world %d!", foo + 2);
        ^
)");
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
    CHECK(diags[2].code == diag::TypoIdentifier);
    CHECK(diags[3].code == diag::MethodReturnMismatch);
    CHECK(diags[4].code == diag::Redefinition);
    CHECK(diags[5].code == diag::NotASubroutine);
}

TEST_CASE("DPI Imports") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    import "DPI-C" pure \begin = function void f(input, output logic[3:0]);

    logic [3:0] r;
    initial f(1, r);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Non-const subroutine check failures") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    import "DPI-C" function int f1(input);
    function void g; endfunction
    task t; endtask
    function int u(output o); endfunction

    if (1) begin : asdf
        function int v; endfunction
    end

    localparam int i = f1(1);
    localparam int j = f2();
    localparam int k = f3();
    localparam int l = f4();
    localparam int m = f5();

    function int f2; g(); endfunction
    function int f3; t(); endfunction
    function int f4;
        automatic logic l;
        return u(l);
    endfunction
    function int f5; return asdf.v(); endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::ConstEvalDPINotConstant);
    CHECK(diags[1].code == diag::ConstEvalVoidNotConstant);
    CHECK(diags[2].code == diag::ConstEvalTaskNotConstant);
    CHECK(diags[3].code == diag::ConstEvalFunctionArgDirection);
    CHECK(diags[4].code == diag::ConstEvalFunctionInsideGenerate);
}

TEST_CASE("Subroutine ref arguments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function void foo;
        ref int a;
        const ref int b;
        ref int c;
    endfunction

    class C;
        int b;
    endclass

    int a;
    const C c = new;
    int d[3];
    initial begin
        foo(c.b, a, d[2]);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Subroutine ref argument errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function void foo;
        ref int a;
        const ref int b;
        ref int c;
        ref int d;
    endfunction

    const int a = 1;
    localparam int b = 2;
    logic [3:0] c;
    
    initial begin
        foo(a, a + 2, b, c);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ConstVarToRef);
    CHECK(diags[1].code == diag::InvalidRefArg);
    CHECK(diags[2].code == diag::InvalidRefArg);
    CHECK(diags[3].code == diag::RefTypeMismatch);
}
