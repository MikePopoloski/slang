// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Definition.h"
#include "slang/ast/Statements.h"
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
#include "slang/text/Json.h"

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

    int arr[3];
    initial begin
        randsequence()
            a: case (f) 0, 1: b("hello"); default: c; endcase | c;
            b(string s): { $display(s); };
            c: { break; };
        endsequence

        arr[0] = randomize with { foreach(arr[i]) i == 1; };
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
            "lifetime": "Static"
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
                "visibility": "Public"
              }
            ],
            "isAbstract": false,
            "isInterface": false,
            "implements": [
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
            "lifetime": "Static"
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

TEST_CASE("JSON dump -- attributes") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire dog, cat;
    (* special *) assign dog = cat;
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
      "name": "m",
      "kind": "Instance",
      "body": {
        "name": "m",
        "kind": "InstanceBody",
        "members": [
          {
            "name": "dog",
            "kind": "Net",
            "type": "logic",
            "netType": {
              "name": "wire",
              "kind": "NetType",
              "type": "logic"
            }
          },
          {
            "name": "cat",
            "kind": "Net",
            "type": "logic",
            "netType": {
              "name": "wire",
              "kind": "NetType",
              "type": "logic"
            }
          },
          {
            "name": "",
            "kind": "ContinuousAssign",
            "attributes": [
              {
                "name": "special",
                "kind": "Attribute",
                "value": "1'b1"
              }
            ],
            "assignment": {
              "kind": "Assignment",
              "type": "logic",
              "left": {
                "kind": "NamedValue",
                "type": "logic",
                "symbol": "dog"
              },
              "right": {
                "kind": "NamedValue",
                "type": "logic",
                "symbol": "cat"
              },
              "isNonBlocking": false
            }
          }
        ],
        "definition": "m"
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

    auto ts = [](string_view str) { return TimeScale::fromString(str).value(); };

    CHECK(compilation.getDefinition("m", compilation.getRoot())->timeScale == ts("10ns/10ps"));
    CHECK(compilation.getDefinition("n", compilation.getRoot())->timeScale == ts("10us/1ns"));
    CHECK(compilation.getDefinition("o", compilation.getRoot())->timeScale == ts("100s/10fs"));
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
    wire foo;
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
    parameter signed bar[2] = '{1,2};
    parameter [31:0] baz[2] = '{1,2};
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
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:7:5: error: $error encountered
    $error;
    ^
source:11:9: note: $info encountered:           43.200000 top.asdf.genblk1:m Hello world 14!
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

    import "DPI-C" function void f8(i);
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
        specparam s5 = j;
    endspecify

    int k = s4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::SpecparamInConstant);
    CHECK(diags[1].code == diag::SpecifyBlockParam);
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

primitive p11 (a, b);
    output reg a;
    input b;
    initial a = 1'b1;
    table 00:; endtable
endprimitive
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 20);
    CHECK(diags[0].code == diag::PrimitiveOutputFirst);
    CHECK(diags[1].code == diag::PrimitiveAnsiMix);
    CHECK(diags[2].code == diag::DuplicateDefinition);
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
    CHECK(diags[19].code == diag::ExpectedUdpSymbol);
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
                    .memberAt<GenerateBlockSymbol>(1)
                    .memberAt<GenerateBlockSymbol>(1)
                    .find<VariableSymbol>("foo");

    std::string path;
    foo.getHierarchicalPath(path);
    CHECK(path == "top.m1[2][1][3].asdf[1].genblk1.foo");
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
    $static_assert(foo * 0, "Stuff %0d", foo / 2);
    $static_assert(foo, "Stuff Stuff %0d", foo / 2);
    $static_assert(bar);

    initial begin
        $static_assert(foo > $bits(bar));
        $static_assert(foo < $bits(bar));
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
    $static_assert(foo * 0, "Stuff %0d", foo / 2);
    ^
source:14:5: error: static assertion failed
    $static_assert(bar);
    ^
source:14:20: error: reference to non-constant variable 'bar' is not allowed in a constant expression
    $static_assert(bar);
                   ^~~
source:9:41: note: declared here
    struct packed { logic [4:1] a, b; } bar;
                                        ^
source:18:9: error: static assertion failed
        $static_assert(foo < $bits(bar));
        ^
source:18:28: note: comparison reduces to (12 < 8)
        $static_assert(foo < $bits(bar));
                       ~~~~^~~~~~~~~~~~
)");
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
    options.allowDupInitialDrivers = true;

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

TEST_CASE("driver checking applied to subroutine ref args") {
    auto tree = SyntaxTree::fromText(R"(
function automatic void f(ref int a);
endfunction

function automatic void g(const ref int a);
endfunction

module m;
    int i;
    always_comb begin
        f(i);
        g(i);
    end
    always_comb begin
        f(i);
        g(i);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
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

    Compilation compilation;
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

TEST_CASE("Subroutine referring to itself in return type") {
    auto tree = SyntaxTree::fromText(R"(
function foo foo;
endfunction

class A;
    extern function bar bar;
endclass

function bar A::bar;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::NotAType);
    CHECK(diags[1].code == diag::RecursiveDefinition);
    CHECK(diags[2].code == diag::RecursiveDefinition);
    CHECK(diags[3].code == diag::NotAType);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
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
    longint i = m.k;
    assign m.o = i;
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

TEST_CASE("Extern interface method errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    extern task t1;
    extern forkjoin function int f1(int i);

    logic l;
    function void f2; endfunction

    modport m(input l);
    modport o(export f1);
endinterface

module n (I.m m);
    function void n.foo(int i, real r); endfunction
    function void m.foo(int i, real r); endfunction
    function void m.l(int i, real r); endfunction
    function void m.f2(); endfunction
    function void m.f1(); endfunction
endmodule

module p (I.o o);
endmodule

module q (I.o o);
    function int o.f1(int i); endfunction
endmodule

module top;
    I i();
    n n1(i);
    p p1(i);
    q q1(i);

    function int n1.foo(int i); endfunction

    real r;
    function int r.foo(int i); endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::MissingExternImpl);
    CHECK(diags[1].code == diag::ExternFuncForkJoin);
    CHECK(diags[2].code == diag::MethodReturnMismatch);
    CHECK(diags[3].code == diag::UndeclaredIdentifier);
    CHECK(diags[4].code == diag::UnknownMember);
    CHECK(diags[5].code == diag::NotASubroutine);
    CHECK(diags[6].code == diag::IfaceMethodNotExtern);
    CHECK(diags[7].code == diag::MissingExportImpl);
    CHECK(diags[8].code == diag::DupInterfaceExternMethod);
    CHECK(diags[9].code == diag::NotAnInterfaceOrPort);
    CHECK(diags[10].code == diag::NotAnInterfaceOrPort);
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
        if (opcode == s1) (i2 => o1) = (5.6, 8.0);
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
        if (int'(g) == 1) (a => z[3]) = 1;
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
    REQUIRE(diags.size() == 17);
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
    CHECK(diags[15].code == diag::InvalidSpecifySource);
    CHECK(diags[16].code == diag::InvalidSpecifyDest);
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
        $setuphold(posedge clk, data, tSU, tHLD, notify, 1:2:3, bar, dclk, ddata);
        $recovery(posedge clk, data, 42);
        $removal(posedge clk, data, 42, );
        $recrem(posedge clk, data, tSU, tHLD, notify, 1:2:3, bar, dclk);
        $recrem(posedge clk, data, tSU, tHLD, notify, 1:2:3, bar, w[0], ddata);
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
        $setuphold(notify, negedge a, 1, 2, , , , asdf);
        $setup(posedge a, a, -12.14);
        $width(a, 1);
        $nochange(edge [1x] a, a, 1, 2);
    endspecify
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 14);
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
    CHECK(diags[10].code == diag::InvalidSpecifySource);
    CHECK(diags[11].code == diag::NegativeTimingLimit);
    CHECK(diags[12].code == diag::TimingCheckEventEdgeRequired);
    CHECK(diags[13].code == diag::NoChangeEdgeRequired);
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

    auto ds = m.membersOfType<ContinuousAssignSymbol>()[0]->getDriveStrength();
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
