// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/text/Json.h"

std::string serialize(Compilation& comp, bool sourceInfo = false, bool detailedTypeInfo = false) {
    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(comp, writer);
    serializer.setIncludeAddresses(false);
    serializer.setIncludeSourceInfo(sourceInfo);
    serializer.setDetailedTypeInfo(detailedTypeInfo);
    serializer.serialize(comp.getRoot());

    return "\n"s + std::string(writer.view());
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
    serialize(compilation);
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

    auto result = serialize(compilation, true);
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
            "name": "STATE",
            "kind": "TypeAlias",
            "source_file": "source",
            "source_line": 6,
            "source_column": 7,
            "target": "enum{STATE_0=1'd0,STATE_1=1'd1}test_enum.STATE"
          },
          {
            "name": "a",
            "kind": "Variable",
            "source_file": "source",
            "source_line": 8,
            "source_column": 11,
            "type": "test_enum.STATE",
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

    auto result = serialize(compilation);
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

    auto result = serialize(compilation);
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
TEST_CASE("JSON dump -- covergroup with an option") {
    auto tree = SyntaxTree::fromText(R"(
class C3;
    logic clk, y, c;

    covergroup g2 ();

        e: coverpoint y iff (clk) {
            option.weight = 2;
        }
        cross e, y {
            option.weight = c;
        }
    endgroup
endclass

)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto result = serialize(compilation);
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
          "name": "C3",
          "kind": "ClassType",
          "members": [
            {
              "name": "clk",
              "kind": "ClassProperty",
              "type": "logic",
              "lifetime": "Automatic",
              "visibility": "Public"
            },
            {
              "name": "y",
              "kind": "ClassProperty",
              "type": "logic",
              "lifetime": "Automatic",
              "visibility": "Public"
            },
            {
              "name": "c",
              "kind": "ClassProperty",
              "type": "logic",
              "lifetime": "Automatic",
              "visibility": "Public"
            },
            {
              "name": "",
              "kind": "CovergroupType",
              "members": [
                {
                  "name": "",
                  "kind": "CovergroupBody",
                  "members": [
                    {
                      "name": "option",
                      "kind": "ClassProperty",
                      "type": "struct{string name;int weight;int goal;string comment;int at_least;int auto_bin_max;int cross_num_print_missing;bit detect_overlap;bit per_instance;bit get_inst_coverage;}C3.s$1",
                      "lifetime": "Automatic",
                      "visibility": "Public"
                    },
                    {
                      "name": "type_option",
                      "kind": "ClassProperty",
                      "type": "struct{int weight;int goal;string comment;bit strobe;bit merge_instances;bit distribute_first;}C3.s$2",
                      "lifetime": "Static",
                      "visibility": "Public"
                    },
                    {
                      "name": "e",
                      "kind": "Coverpoint",
                      "members": [
                        {
                          "name": "option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;int at_least;int auto_bin_max;bit detect_overlap;}C3.e.s$3",
                          "lifetime": "Automatic",
                          "visibility": "Public"
                        },
                        {
                          "name": "type_option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;}C3.e.s$4",
                          "lifetime": "Static",
                          "visibility": "Public"
                        }
                      ],
                      "options": [
                        {
                          "expr": {
                            "kind": "Assignment",
                            "type": "int",
                            "left": {
                              "kind": "MemberAccess",
                              "type": "int",
                              "member": "weight",
                              "value": {
                                "kind": "NamedValue",
                                "type": "struct{int weight;int goal;string comment;int at_least;int auto_bin_max;bit detect_overlap;}C3.e.s$3",
                                "symbol": "option"
                              }
                            },
                            "right": {
                              "kind": "IntegerLiteral",
                              "type": "int",
                              "value": "2",
                              "constant": "2"
                            },
                            "isNonBlocking": false
                          }
                        }
                      ],
                      "iff": {
                        "kind": "NamedValue",
                        "type": "logic",
                        "symbol": "clk"
                      }
                    },
                    {
                      "name": "y",
                      "kind": "Coverpoint",
                      "members": [
                        {
                          "name": "option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;int at_least;int auto_bin_max;bit detect_overlap;}C3.y.s$5",
                          "lifetime": "Automatic",
                          "visibility": "Public"
                        },
                        {
                          "name": "type_option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;}C3.y.s$6",
                          "lifetime": "Static",
                          "visibility": "Public"
                        }
                      ]
                    },
                    {
                      "name": "",
                      "kind": "CoverCross",
                      "members": [
                        {
                          "name": "option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;int at_least;int cross_num_print_missing;}C3.s$7",
                          "lifetime": "Automatic",
                          "visibility": "Public"
                        },
                        {
                          "name": "type_option",
                          "kind": "ClassProperty",
                          "type": "struct{int weight;int goal;string comment;}C3.s$8",
                          "lifetime": "Static",
                          "visibility": "Public"
                        },
                        {
                          "name": "",
                          "kind": "CoverCrossBody",
                          "members": [
                            {
                              "name": "CrossValType",
                              "kind": "TypeAlias",
                              "target": "struct{logic[0:0] e;logic[0:0] y;}C3.s$9"
                            },
                            {
                              "name": "CrossQueueType",
                              "kind": "TypeAlias",
                              "target": "C3.CrossValType$[$]"
                            }
                          ]
                        }
                      ],
                      "targets": [
                        {
                          "coverpoint": "e"
                        },
                        {
                          "coverpoint": "y"
                        }
                      ],
                      "options": [
                        {
                          "expr": {
                            "kind": "Assignment",
                            "type": "int",
                            "left": {
                              "kind": "MemberAccess",
                              "type": "int",
                              "member": "weight",
                              "value": {
                                "kind": "NamedValue",
                                "type": "struct{int weight;int goal;string comment;int at_least;int cross_num_print_missing;}C3.s$7",
                                "symbol": "option"
                              }
                            },
                            "right": {
                              "kind": "Conversion",
                              "type": "int",
                              "operand": {
                                "kind": "Conversion",
                                "type": "logic[31:0]",
                                "operand": {
                                  "kind": "NamedValue",
                                  "type": "logic",
                                  "symbol": "c"
                                }
                              }
                            },
                            "isNonBlocking": false
                          }
                        }
                      ]
                    }
                  ]
                }
              ]
            },
            {
              "name": "g2",
              "kind": "ClassProperty",
              "type": "",
              "lifetime": "Automatic",
              "flags": "const",
              "visibility": "Public"
            }
          ],
          "isAbstract": false,
          "isInterface": false,
          "isFinal": false,
          "implements": [
          ]
        }
      ]
    }
  ]
})");
}

TEST_CASE("Serializing uninstantiated defs with implicit named connections") {
    auto tree = SyntaxTree::fromText(R"(
module top;
endmodule

module n #(parameter int j);
    int foo;
    m m1(
        .foo,
        .bar()
    );
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto result = serialize(compilation);
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
      "name": "top",
      "kind": "Instance",
      "body": {
        "name": "top",
        "kind": "InstanceBody",
        "definition": "top"
      },
      "connections": [
      ]
    },
    {
      "name": "",
      "kind": "Instance",
      "body": {
        "name": "n",
        "kind": "InstanceBody",
        "members": [
          {
            "name": "j",
            "kind": "Parameter",
            "type": "int",
            "value": "<unset>",
            "isLocal": false,
            "isPort": true,
            "isBody": false
          },
          {
            "name": "foo",
            "kind": "Variable",
            "type": "int",
            "lifetime": "Static"
          },
          {
            "name": "m1",
            "kind": "UninstantiatedDef",
            "definitionName": "m",
            "parameters": [
            ],
            "ports": [
              {
                "name": "foo",
                "expr": {
                  "kind": "Simple",
                  "expr": {
                    "kind": "NamedValue",
                    "type": "int",
                    "symbol": "foo"
                  }
                }
              },
              {
                "name": "bar",
                "expr": {
                  "kind": "Invalid"
                }
              }
            ]
          }
        ],
        "definition": "n"
      },
      "connections": [
      ]
    }
  ]
})");
}

TEST_CASE("Serializing types and type aliase targets") {
    auto tree = SyntaxTree::fromText(R"(
typedef union packed {
    logic [31:0] inst;
} INST;

typedef struct packed {
    INST inst;
    logic another_signal;
} CONTAINER;

typedef enum logic [1:0] {
    BYTE   = 2'h0,
    HALF   = 2'h1,
    WORD   = 2'h2,
    DOUBLE = 2'h3
} MEM_SIZE;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto result = serialize(compilation, false, true);
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
          "name": "INST",
          "kind": "TypeAlias",
          "target": {
            "name": "",
            "kind": "PackedUnionType",
            "members": [
              {
                "name": "inst",
                "kind": "Field",
                "type": {
                  "name": "",
                  "kind": "PackedArrayType",
                  "elementType": {
                    "name": "logic",
                    "kind": "ScalarType"
                  },
                  "range": "[31:0]"
                },
                "lifetime": "Automatic",
                "bitOffset": 0,
                "fieldIndex": 0
              }
            ],
            "isTagged": false,
            "isSoft": false
          }
        },
        {
          "name": "CONTAINER",
          "kind": "TypeAlias",
          "target": {
            "name": "",
            "kind": "PackedStructType",
            "members": [
              {
                "name": "inst",
                "kind": "Field",
                "type": {
                  "name": "INST",
                  "kind": "TypeAlias",
                  "target": {
                    "name": "",
                    "kind": "PackedUnionType",
                    "members": [
                      {
                        "name": "inst",
                        "kind": "Field",
                        "type": {
                          "name": "",
                          "kind": "PackedArrayType",
                          "elementType": {
                            "name": "logic",
                            "kind": "ScalarType"
                          },
                          "range": "[31:0]"
                        },
                        "lifetime": "Automatic",
                        "bitOffset": 0,
                        "fieldIndex": 0
                      }
                    ],
                    "isTagged": false,
                    "isSoft": false
                  }
                },
                "lifetime": "Automatic",
                "bitOffset": 1,
                "fieldIndex": 0
              },
              {
                "name": "another_signal",
                "kind": "Field",
                "type": {
                  "name": "logic",
                  "kind": "ScalarType"
                },
                "lifetime": "Automatic",
                "bitOffset": 0,
                "fieldIndex": 1
              }
            ]
          }
        },
        {
          "name": "MEM_SIZE",
          "kind": "TypeAlias",
          "target": {
            "name": "MEM_SIZE",
            "kind": "EnumType",
            "members": [
              {
                "name": "BYTE",
                "kind": "EnumValue",
                "initializer": {
                  "kind": "Conversion",
                  "type": {
                    "name": "",
                    "kind": "PackedArrayType",
                    "elementType": {
                      "name": "logic",
                      "kind": "ScalarType"
                    },
                    "range": "[1:0]"
                  },
                  "operand": {
                    "kind": "IntegerLiteral",
                    "type": {
                      "name": "",
                      "kind": "PackedArrayType",
                      "elementType": {
                        "name": "bit",
                        "kind": "ScalarType"
                      },
                      "range": "[1:0]"
                    },
                    "value": "2'b0",
                    "constant": "2'b0"
                  },
                  "constant": "2'b0"
                },
                "value": "2'b0"
              },
              {
                "name": "HALF",
                "kind": "EnumValue",
                "initializer": {
                  "kind": "Conversion",
                  "type": {
                    "name": "",
                    "kind": "PackedArrayType",
                    "elementType": {
                      "name": "logic",
                      "kind": "ScalarType"
                    },
                    "range": "[1:0]"
                  },
                  "operand": {
                    "kind": "IntegerLiteral",
                    "type": {
                      "name": "",
                      "kind": "PackedArrayType",
                      "elementType": {
                        "name": "bit",
                        "kind": "ScalarType"
                      },
                      "range": "[1:0]"
                    },
                    "value": "2'b1",
                    "constant": "2'b1"
                  },
                  "constant": "2'b1"
                },
                "value": "2'b1"
              },
              {
                "name": "WORD",
                "kind": "EnumValue",
                "initializer": {
                  "kind": "Conversion",
                  "type": {
                    "name": "",
                    "kind": "PackedArrayType",
                    "elementType": {
                      "name": "logic",
                      "kind": "ScalarType"
                    },
                    "range": "[1:0]"
                  },
                  "operand": {
                    "kind": "IntegerLiteral",
                    "type": {
                      "name": "",
                      "kind": "PackedArrayType",
                      "elementType": {
                        "name": "bit",
                        "kind": "ScalarType"
                      },
                      "range": "[1:0]"
                    },
                    "value": "2'b10",
                    "constant": "2'b10"
                  },
                  "constant": "2'b10"
                },
                "value": "2'b10"
              },
              {
                "name": "DOUBLE",
                "kind": "EnumValue",
                "initializer": {
                  "kind": "Conversion",
                  "type": {
                    "name": "",
                    "kind": "PackedArrayType",
                    "elementType": {
                      "name": "logic",
                      "kind": "ScalarType"
                    },
                    "range": "[1:0]"
                  },
                  "operand": {
                    "kind": "IntegerLiteral",
                    "type": {
                      "name": "",
                      "kind": "PackedArrayType",
                      "elementType": {
                        "name": "bit",
                        "kind": "ScalarType"
                      },
                      "range": "[1:0]"
                    },
                    "value": "2'b11",
                    "constant": "2'b11"
                  },
                  "constant": "2'b11"
                },
                "value": "2'b11"
              }
            ],
            "baseType": {
              "name": "",
              "kind": "PackedArrayType",
              "elementType": {
                "name": "logic",
                "kind": "ScalarType"
              },
              "range": "[1:0]"
            }
          }
        }
      ]
    }
  ]
})");
}
