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

    wire bar;
    assign (strong1, supply0) #(3,2,1) bar = 1;
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
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::DelayNotNumeric);
    CHECK(diags[1].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[2].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[3].code == diag::DynamicNotProcedural);
    CHECK(diags[4].code == diag::DynamicNotProcedural);
    CHECK(diags[5].code == diag::DynamicNotProcedural);
    CHECK(diags[6].code == diag::DynamicNotProcedural);
    CHECK(diags[7].code == diag::Delay3OnVar);
    CHECK(diags[8].code == diag::NonProceduralFuncArg);
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

function int foo(int a, output logic b);
endfunction

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

    initial begin
        randsequence()
            a: case (f) 0, 1: b("hello"); default: c; endcase | c;
            b(string s): { $display(s); };
            c: { break; };
        endsequence
    end

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

    class C;
        int i;
    endclass

    C c = new;
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
            "type": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.STATE",
            "initializer": {
              "kind": "NamedValue",
              "type": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.STATE",
              "symbol": "STATE_0",
              "constant": "1'b0"
            },
            "lifetime": "Static",
            "isConstant": false,
            "isCompilerGenerated": false
          },
          {
            "name": "C",
            "kind": "ClassType",
            "members": [
              {
                "name": "i",
                "kind": "ClassProperty",
                "type": "int",
                "lifetime": "Automatic",
                "isConstant": false,
                "isCompilerGenerated": false,
                "visibility": "Public"
              }
            ]
          },
          {
            "name": "c",
            "kind": "Variable",
            "type": "C",
            "initializer": {
              "kind": "NewClass",
              "type": "C"
            },
            "lifetime": "Static",
            "isConstant": false,
            "isCompilerGenerated": false
          }
        ],
        "definition": "test_enum"
      },
      "connections": [
      ]
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
    function automatic foo;
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
    function automatic foo;
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
    logic foo;
    pullup (supply0, pull1) (foo);
    pmos #3 asdf [3:0][4][5] (foo, 2, 3), blah (foo, 4, 5), (foo, 5, 6);
    rtranif1 (foo, foo, 1), asdf2(foo, foo, 2);

    pmos #6 (a, b, c);

    and (a, 1, 2, 3, 4, 5, 6, 7, 8);
    buf (a, b, c, 1);

    logic [3:0] out, in, en;
    bufif0 ar[3:0] (out, in, en);

    wire [7:0] value1;
    wire [7:0] value2;
    cmos buffer[7:0](value2, value1, 1'b1, 1'b0);
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
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:7:5: error: $error encountered
    $error;
    ^
source:11:9: note: $info encountered:           43.200000 top.asdf:m Hello world 14!
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
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InfoTask);
    CHECK(diags[1].code == diag::ConstEvalNonConstVariable);
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
    import "DPI-C" context \begin = function void f1(input, output logic[3:0]);
    import "asdf" function void f2();
    import "DPI" function void f3();
    import "DPI-C" function void f4(ref i);
    import "DPI-C" pure function void f5(output i);
    import "DPI-C" pure function event f6(event e);
    import "DPI-C" function byte unsigned f7();

    logic [3:0] r;
    initial f1(1, r);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::ExpectedDPISpecString);
    CHECK(diags[1].code == diag::DPISpecDisallowed);
    CHECK(diags[2].code == diag::DPIRefArg);
    CHECK(diags[3].code == diag::DPIPureReturn);
    CHECK(diags[4].code == diag::DPIPureArg);
    CHECK(diags[5].code == diag::InvalidDPIReturnType);
    CHECK(diags[6].code == diag::InvalidDPIArgType);
}

TEST_CASE("DPI Exports") {
    auto tree = SyntaxTree::fromText(R"(
function bar; endfunction

module m;
    int boo;
    function foo; endfunction

    export "DPI-C" \begin = function foo;
    export "DPI" function baz;
    export "DPI-C" function boo;
    export "DPI-C" task foo;
    export "DPI-C" function bar;

    function event f1; endfunction
    function int f2(event e); endfunction

    export "DPI-C" function f1;
    export "DPI-C" function f2;
    export "DPI-C" function foo;

    function automatic void f3(ref r); endfunction
    export "DPI-C" function f3;

    import "DPI-C" function void f4;
    export "DPI-C" function f4;

    function void f5; endfunction
    export "DPI-C" \0a = function f5;

    import "DPI-C" a$ = function void f6;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 12);
    CHECK(diags[0].code == diag::DPISpecDisallowed);
    CHECK(diags[1].code == diag::TypoIdentifier);
    CHECK(diags[2].code == diag::NotASubroutine);
    CHECK(diags[3].code == diag::DPIExportKindMismatch);
    CHECK(diags[4].code == diag::DPIExportDifferentScope);
    CHECK(diags[5].code == diag::InvalidDPIReturnType);
    CHECK(diags[6].code == diag::InvalidDPIArgType);
    CHECK(diags[7].code == diag::DPIExportDuplicate);
    CHECK(diags[8].code == diag::DPIRefArg);
    CHECK(diags[9].code == diag::DPIExportImportedFunc);
    CHECK(diags[10].code == diag::InvalidDPICIdentifier);
    CHECK(diags[11].code == diag::InvalidDPICIdentifier);
}

TEST_CASE("DPI signature checking") {
    auto tree = SyntaxTree::fromText(R"(
import "DPI-C" function int foo(int a, output b);

function longint bar; endfunction
export "DPI-C" foo = function bar;

import "DPI-C" foo = function longint f1;

function int f2(int a, output b); endfunction
export "DPI-C" asdf = function f2;

module m1;
    function int f3(longint a, output b); endfunction
    export "DPI-C" asdf = function f3;
endmodule

module m2;
    function int f4(longint a, output b, input c); endfunction
    export "DPI-C" asdf = function f4;
endmodule

module m3;
    function int f5(int a, input b); endfunction
    export "DPI-C" asdf = function f5;
endmodule

module m4;
    function int asdf(int a, output b); endfunction
    export "DPI-C" function asdf;

    function int blah(int a, output b); endfunction
    export "DPI-C" asdf = function blah;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::DPISignatureMismatch);
    CHECK(diags[1].code == diag::DPISignatureMismatch);
    CHECK(diags[2].code == diag::DPISignatureMismatch);
    CHECK(diags[3].code == diag::DPISignatureMismatch);
    CHECK(diags[4].code == diag::DPISignatureMismatch);
    CHECK(diags[5].code == diag::DPIExportDuplicateCId);
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

    if (t()) begin end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ConstEvalDPINotConstant);
    CHECK(diags[1].code == diag::ConstEvalVoidNotConstant);
    CHECK(diags[2].code == diag::TaskFromFunction);
    CHECK(diags[3].code == diag::ConstEvalFunctionArgDirection);
    CHECK(diags[4].code == diag::ConstEvalFunctionInsideGenerate);
    CHECK(diags[5].code == diag::ConstEvalTaskNotConstant);
}

TEST_CASE("Subroutine ref arguments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function automatic void foo;
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
    function automatic void foo;
        ref int a;
        const ref int b;
        ref int c;
        ref int d;
        ref logic e;
    endfunction

    const int a = 1;
    localparam int b = 2;
    logic [3:0] c;
    
    initial begin
        foo(a, a + 2, b, c, c[0]);
    end

    function void bar;
        ref r;
    endfunction
    function void baz(ref r);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::ConstVarToRef);
    CHECK(diags[1].code == diag::InvalidRefArg);
    CHECK(diags[2].code == diag::InvalidRefArg);
    CHECK(diags[3].code == diag::RefTypeMismatch);
    CHECK(diags[4].code == diag::InvalidRefArg);
    CHECK(diags[5].code == diag::RefArgAutomaticFunc);
    CHECK(diags[6].code == diag::RefArgAutomaticFunc);
}

TEST_CASE("specparams") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    specparam s1 = 1:2:3;
    specparam s2 = 3.14;
    specparam [31:0] s3 = s1 + s2;

    int i = s3;
    localparam int j = s3;

    specify 
        specparam s4 = 2:3:4;
    endspecify

    int k = s4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SpecparamInConstant);
}

TEST_CASE("user-defined primitives") {
    auto tree = SyntaxTree::fromText(R"(
primitive srff (q, s, r);
    output q; reg q;
    input s, r;
    initial q = 1'b1;
    table
        // s r q q+
        1 0 : ? : 1 ;
        f 0 : 1 : - ;
        0 r : ? : 0 ;
        0 f : 0 : - ;
        1 1 : ? : 0 ;
    endtable
endprimitive : srff

primitive p2 (output reg a = 1'bx, input b, input c);
    table 00:0; endtable
endprimitive

module m;
    logic q;
    srff sf1(q, 1, 0);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("UDP errors") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (input a, b, output c);
    output b;
    table 00:0; endtable
endprimitive

primitive p1 (output a, input b);
    table 00:0; endtable
endprimitive

primitive p2 (output a);
    table 00:0; endtable
endprimitive

primitive p3 (a, b);
    input b;
    output a;
    output reg a;
    table 00:0; endtable
endprimitive

primitive p4 (a, b);
    input b;
    output a;
    reg a;
    reg a;
    input c;
    output d;
    table 00:0; endtable
endprimitive

primitive p5 (a, b);
    reg a;
    input b;
    output reg a;
    table 00:0; endtable
endprimitive

primitive p6 (a, b, c);
    input b;
    output a;
    reg b;
    table 00:0; endtable
endprimitive

primitive p7 (a, b, c);
    output b;
    output a;
    initial a = 1;
    table 00:0; endtable
endprimitive

primitive p8 (a, b);
    output reg a = 1;
    input b;
    initial a = 1'bx;
    table 00:0; endtable
endprimitive

primitive p9 (a, b);
    output reg a;
    input b;
    initial c = 1'bx;
    table 00:0; endtable
endprimitive

primitive p10 (a, b);
    output reg a;
    input b;
    initial a = 3;
    table 00:0; endtable
endprimitive

module p10; endmodule

module m;
endmodule

primitive m(output a, input b);
    table 00:0; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 19);
    CHECK(diags[0].code == diag::PrimitiveOutputFirst);
    CHECK(diags[1].code == diag::PrimitiveAnsiMix);
    CHECK(diags[2].code == diag::Redefinition);
    CHECK(diags[3].code == diag::PrimitiveTwoPorts);
    CHECK(diags[4].code == diag::PrimitivePortDup);
    CHECK(diags[5].code == diag::PrimitiveRegDup);
    CHECK(diags[6].code == diag::PrimitivePortUnknown);
    CHECK(diags[7].code == diag::PrimitivePortUnknown);
    CHECK(diags[8].code == diag::PrimitivePortDup);
    CHECK(diags[9].code == diag::PrimitivePortMissing);
    CHECK(diags[10].code == diag::PrimitiveRegInput);
    CHECK(diags[11].code == diag::PrimitivePortMissing);
    CHECK(diags[12].code == diag::PrimitiveDupOutput);
    CHECK(diags[13].code == diag::PrimitiveInitialInComb);
    CHECK(diags[14].code == diag::PrimitiveDupInitial);
    CHECK(diags[15].code == diag::PrimitiveWrongInitial);
    CHECK(diags[16].code == diag::PrimitiveInitVal);
    CHECK(diags[17].code == diag::Redefinition);
    CHECK(diags[18].code == diag::Redefinition);
}

TEST_CASE("UDP instances error checking") {
    auto tree = SyntaxTree::fromText(R"(
primitive p1 (output a, input b);
    table 00:0; endtable
endprimitive

module m;
    logic foo[3];
    p1 #(3, 4) (a, b);
    p1 #(foo) (a, b);
    p1 #(.baz(1), .bar(2)) (a, b);
    p1 #(3, 4, 5) (a, b);
    p1 #3 (a, b);
    p1 (supply0, strong1) #(1:2:3, 3:2:1) asdf(a, b);
    p1 (,);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::DelayNotNumeric);
    CHECK(diags[1].code == diag::ExpectedNetDelay);
    CHECK(diags[2].code == diag::Delay3UdpNotAllowed);
    CHECK(diags[3].code == diag::EmptyUdpPort);
    CHECK(diags[4].code == diag::EmptyUdpPort);
}

TEST_CASE("Module mixup with primitive instance") {
    auto tree = SyntaxTree::fromText(R"(
module n;
endmodule

module m;
    n #  3 n1();
    n (supply0, strong1) n2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InstanceWithDelay);
    CHECK(diags[1].code == diag::InstanceWithStrength);
}

TEST_CASE("Module escaped name instead of primitive") {
    auto tree = SyntaxTree::fromText(R"(
module \and (output a, input b, c);
endmodule

module m;
    \and a(a1, b1, c1);
    and (a2, b2, c2);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Subroutine return lookup location regress") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    localparam w = 8;
    function [w-1:0] copy;
        input [w-1:0] w;
        begin
            copy = w;
        end
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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

TEST_CASE("Default lifetimes for subroutines") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo; endfunction
    initial begin : baz
        int bar;
    end
endmodule

module automatic n;
    function foo; endfunction
    initial begin : baz
        int bar;
    end
endmodule

package automatic p;
    function foo; endfunction
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto func = [&](string_view name) {
        return root.lookupName<SubroutineSymbol>(name).defaultLifetime;
    };

    CHECK(func("m.foo") == VariableLifetime::Static);
    CHECK(func("n.foo") == VariableLifetime::Automatic);
    CHECK(func("p::foo") == VariableLifetime::Automatic);

    CHECK(root.lookupName<VariableSymbol>("m.baz.bar").lifetime == VariableLifetime::Static);

    auto& block = root.lookupName<StatementBlockSymbol>("n.baz");
    CHECK(block.memberAt<VariableSymbol>(0).lifetime == VariableLifetime::Automatic);
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
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::MultipleDefaultInputSkew);
    CHECK(diags[1].code == diag::MultipleDefaultOutputSkew);
    CHECK(diags[2].code == diag::ExpressionNotAssignable);
    CHECK(diags[3].code == diag::InvalidClockingSignal);
    CHECK(diags[4].code == diag::MultipleDefaultClocking);
    CHECK(diags[5].code == diag::NotAClockingBlock);
    CHECK(diags[6].code == diag::MultipleGlobalClocking);
    CHECK(diags[7].code == diag::GlobalClockingGenerate);
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
    modport test (input clk, enable, cmd);
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
            let my_let(x) = !x || b && c[i];
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
            let my_let(x) = !x || b && c[i];
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
    m #(.bar(50)) m1();
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
