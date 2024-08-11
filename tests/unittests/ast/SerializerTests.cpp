// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/text/Json.h"

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
        int unsigned i = 32'(200'd12924697071141057419865760813593169586965814232826232910156);
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
    serializer.setIncludeSourceInfo(true);
    serializer.serialize(compilation.getRoot());

    std::string result = "\n"s + std::string(writer.view());
    CHECK(result == R"(
{
  "name": "$root",
  "kind": "Root",
  "source_file": "",
  "source_line": 0,
  "source_column": 0,
  "members": [
    {
      "name": "",
      "kind": "CompilationUnit",
      "source_file": "",
      "source_line": 0,
      "source_column": 0
    },
    {
      "name": "test_enum",
      "kind": "Instance",
      "source_file": "source",
      "source_line": 2,
      "source_column": 8,
      "body": {
        "name": "test_enum",
        "kind": "InstanceBody",
        "source_file": "source",
        "source_line": 2,
        "source_column": 8,
        "members": [
          {
            "name": "STATE_0",
            "kind": "TransparentMember",
            "source_file": "source",
            "source_line": 4,
            "source_column": 9
          },
          {
            "name": "STATE_1",
            "kind": "TransparentMember",
            "source_file": "source",
            "source_line": 5,
            "source_column": 9
          },
          {
            "name": "STATE",
            "kind": "TypeAlias",
            "source_file": "source",
            "source_line": 6,
            "source_column": 7,
            "target": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.e$1"
          },
          {
            "name": "a",
            "kind": "Variable",
            "source_file": "source",
            "source_line": 8,
            "source_column": 11,
            "type": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.STATE",
            "initializer": {
              "source_file_start": "source",
              "source_file_end": "source",
              "source_line_start": 8,
              "source_line_end": 8,
              "source_column_start": 15,
              "source_column_end": 22,
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
            "source_file": "source",
            "source_line": 10,
            "source_column": 11,
            "members": [
              {
                "name": "i",
                "kind": "ClassProperty",
                "source_file": "source",
                "source_line": 11,
                "source_column": 22,
                "type": "int unsigned",
                "initializer": {
                  "source_file_start": "source",
                  "source_file_end": "source",
                  "source_line_start": 11,
                  "source_line_end": 11,
                  "source_column_start": 26,
                  "source_column_end": 95,
                  "kind": "Conversion",
                  "type": "bit[31:0]",
                  "operand": {
                    "source_file_start": "source",
                    "source_file_end": "source",
                    "source_line_start": 11,
                    "source_line_end": 11,
                    "source_column_start": 29,
                    "source_column_end": 95,
                    "kind": "IntegerLiteral",
                    "type": "bit[199:0]",
                    "value": "200'h20f1c22386aad976de4999f1b69e783e821874fb88b47314c",
                    "constant": "200'h20f1c22386aad976de4999f1b69e783e821874fb88b47314c"
                  },
                  "constant": "32'd2336698700"
                },
                "lifetime": "Automatic",
                "visibility": "Public"
              }
            ],
            "isAbstract": false,
            "isInterface": false,
            "isFinal": false,
            "implements": [
            ]
          },
          {
            "name": "c",
            "kind": "Variable",
            "source_file": "source",
            "source_line": 14,
            "source_column": 7,
            "type": "C",
            "initializer": {
              "source_file_start": "source",
              "source_file_end": "source",
              "source_line_start": 14,
              "source_line_end": 14,
              "source_column_start": 11,
              "source_column_end": 14,
              "kind": "NewClass",
              "type": "C",
              "isSuperClass": false
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

TEST_CASE("JSON dump -- sequence with `iff` clause") {
    auto tree = SyntaxTree::fromText(R"(
logic x, y;

sequence s (ev);
    @(ev) x ##1 y;
endsequence

module m(input y1, input x1, input clk);
    cover property (s(((x1 iff y1) or negedge clk)));
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
      "kind": "CompilationUnit",
      "members": [
        {
          "name": "x",
          "kind": "Variable",
          "type": "logic",
          "lifetime": "Static"
        },
        {
          "name": "y",
          "kind": "Variable",
          "type": "logic",
          "lifetime": "Static"
        },
        {
          "name": "s",
          "kind": "Sequence",
          "members": [
            {
              "name": "ev",
              "kind": "AssertionPort"
            }
          ]
        }
      ]
    },
    {
      "name": "m",
      "kind": "Instance",
      "body": {
        "name": "m",
        "kind": "InstanceBody",
        "members": [
          {
            "name": "y1",
            "kind": "Port",
            "type": "logic",
            "direction": "In",
            "internalSymbol": "y1"
          },
          {
            "name": "y1",
            "kind": "Net",
            "type": "logic",
            "netType": {
              "name": "wire",
              "kind": "NetType",
              "type": "logic"
            }
          },
          {
            "name": "x1",
            "kind": "Port",
            "type": "logic",
            "direction": "In",
            "internalSymbol": "x1"
          },
          {
            "name": "x1",
            "kind": "Net",
            "type": "logic",
            "netType": {
              "name": "wire",
              "kind": "NetType",
              "type": "logic"
            }
          },
          {
            "name": "clk",
            "kind": "Port",
            "type": "logic",
            "direction": "In",
            "internalSymbol": "clk"
          },
          {
            "name": "clk",
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
            "kind": "ProceduralBlock",
            "procedureKind": "Always",
            "body": {
              "kind": "ConcurrentAssertion",
              "propertySpec": {
                "kind": "Simple",
                "expr": {
                  "kind": "AssertionInstance",
                  "type": "sequence",
                  "symbol": "s",
                  "body": {
                    "kind": "Clocking",
                    "clocking": {
                      "kind": "SignalEvent",
                      "expr": {
                        "kind": "ClockingEvent",
                        "type": "void",
                        "timingControl": {
                          "kind": "EventList",
                          "events": [
                            {
                              "kind": "SignalEvent",
                              "expr": {
                                "kind": "NamedValue",
                                "type": "logic",
                                "symbol": "x1"
                              },
                              "edge": "None",
                              "iff": {
                                "kind": "NamedValue",
                                "type": "logic",
                                "symbol": "y1"
                              }
                            },
                            {
                              "kind": "SignalEvent",
                              "expr": {
                                "kind": "NamedValue",
                                "type": "logic",
                                "symbol": "clk"
                              },
                              "edge": "NegEdge"
                            }
                          ]
                        }
                      },
                      "edge": "None"
                    },
                    "expr": {
                      "kind": "SequenceConcat",
                      "elements": [
                        {
                          "sequence": {
                            "kind": "Simple",
                            "expr": {
                              "kind": "NamedValue",
                              "type": "logic",
                              "symbol": "x"
                            }
                          },
                          "min": 0,
                          "max": 0
                        },
                        {
                          "sequence": {
                            "kind": "Simple",
                            "expr": {
                              "kind": "NamedValue",
                              "type": "logic",
                              "symbol": "y"
                            }
                          },
                          "min": 1,
                          "max": 1
                        }
                      ]
                    }
                  },
                  "isRecursiveProperty": false,
                  "localVars": [
                  ]
                }
              },
              "ifTrue": {
                "kind": "Empty"
              },
              "assertionKind": "CoverProperty"
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
