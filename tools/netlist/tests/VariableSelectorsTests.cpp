//------------------------------------------------------------------------------
//! @file VariableSelectorsTests.cpp
//! @brief Tests for handling of variable selectors.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "NetlistTest.h"
#include "Test.h"
#include <stdexcept>

#include "slang/util/Util.h"

/// Helper method to extract a variable reference from a netlist and return the
/// bit range associated with it.
ConstantRange getBitRange(Netlist& netlist, std::string_view variableSyntax) {
    auto* node = netlist.lookupVariableReference(variableSyntax);
    if (node == nullptr) {
        SLANG_THROW(std::runtime_error(fmt::format("Could not find node {}", variableSyntax)));
    }
    return node->bounds;
}

//===---------------------------------------------------------------------===//
// Scalar selectors.
//===---------------------------------------------------------------------===//

TEST_CASE("Scalar element and range") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  int foo;
  always_comb begin
    foo = 0;
    foo[0] = 0;
    foo[1] = 0;
    foo[7:7] = 0;
    foo[1:0] = 0;
    foo[3:1] = 0;
    foo[7:4] = 0;
    foo[a] = 0;
    foo[a+:1] = 0;
    foo[a-:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(0, 0));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[7:7]") == ConstantRange(7, 7));
    CHECK(getBitRange(netlist, "foo[1:0]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[3:1]") == ConstantRange(1, 3));
    CHECK(getBitRange(netlist, "foo[7:4]") == ConstantRange(4, 7));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo[a-:1]") == ConstantRange(0, 31));
}

//===---------------------------------------------------------------------===//
// Packed array selectors.
//===---------------------------------------------------------------------===//

TEST_CASE("Packed 1D array element and range") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic [3:0] foo;
  always_comb begin
    foo = 0;
    foo[0] = 0;
    foo[1] = 0;
    foo[2] = 0;
    foo[3] = 0;
    foo[3:3] = 0;
    foo[1:0] = 0;
    foo[3:0] = 0;
    foo[2:1] = 0;
    foo[a] = 0;
    foo[a+:1] = 0;
    foo[a-:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(0, 0));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[2]") == ConstantRange(2, 2));
    CHECK(getBitRange(netlist, "foo[3]") == ConstantRange(3, 3));
    CHECK(getBitRange(netlist, "foo[3:3]") == ConstantRange(3, 3));
    CHECK(getBitRange(netlist, "foo[1:0]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[3:0]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[2:1]") == ConstantRange(1, 2));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[a-:1]") == ConstantRange(0, 3));
}

TEST_CASE("Packed 1D array element and range non-zero indexed") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic [7:4] foo;
  always_comb begin
    foo = 0;
    foo[4] = 0;
    foo[5] = 0;
    foo[6] = 0;
    foo[7] = 0;
    foo[7:7] = 0;
    foo[5:4] = 0;
    foo[7:4] = 0;
    foo[6:5] = 0;
    foo[a] = 0;
    foo[a+:1] = 0;
    foo[a-:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[4]") == ConstantRange(0, 0));
    CHECK(getBitRange(netlist, "foo[5]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[6]") == ConstantRange(2, 2));
    CHECK(getBitRange(netlist, "foo[7]") == ConstantRange(3, 3));
    CHECK(getBitRange(netlist, "foo[7:7]") == ConstantRange(3, 3));
    CHECK(getBitRange(netlist, "foo[5:4]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[7:4]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[6:5]") == ConstantRange(1, 2));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[a-:1]") == ConstantRange(0, 3));
}

TEST_CASE("Packed 2D array element and range") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic [3:0] [1:0] foo;
  always_comb begin
    foo = 0;
    foo[0] = 0;
    foo[1] = 0;
    foo[2] = 0;
    foo[3] = 0;
    foo[0][1] = 0;
    foo[1][1] = 0;
    foo[2][1] = 0;
    foo[3][1] = 0;
    foo[1:0] = 0;
    foo[3:2] = 0;
    foo[a] = 0;
    foo[a][1] = 0;
    foo[a][a] = 0;
    foo[a+:1] = 0;
    foo[a-:1] = 0;
    foo[1][a] = 0;
    foo[1][a+:1] = 0;
    foo[1][a-:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[2]") == ConstantRange(4, 5));
    CHECK(getBitRange(netlist, "foo[3]") == ConstantRange(6, 7));
    CHECK(getBitRange(netlist, "foo[0][1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[1][1]") == ConstantRange(3, 3));
    CHECK(getBitRange(netlist, "foo[2][1]") == ConstantRange(5, 5));
    CHECK(getBitRange(netlist, "foo[3][1]") == ConstantRange(7, 7));
    CHECK(getBitRange(netlist, "foo[1:0]") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[3:2]") == ConstantRange(4, 7));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a][1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a][a]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a-:1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[1][a]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[1][a+:1]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[1][a-:1]") == ConstantRange(2, 3));
}

TEST_CASE("Packed 2D array element and range, non-zero indexing") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic [7:4] [3:2] foo;
  always_comb begin
    foo = 0;
    foo[4] = 0;
    foo[4][3] = 0;
    foo[5:4] = 0;
    foo[a] = 0;
    foo[a+:1] = 0;
    foo[a-:1] = 0;
    foo[5][a] = 0;
    foo[5][a+:1] = 0;
    foo[5][a-:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[4]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[4][3]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[5:4]") == ConstantRange(0, 3));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a-:1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[5][a]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[5][a+:1]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[5][a-:1]") == ConstantRange(2, 3));
}

//===---------------------------------------------------------------------===//
// Unpacked array selectors.
//===---------------------------------------------------------------------===//

TEST_CASE("Unpacked 1D array element") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic foo [2:0];
  logic bar [2:0];
  always_comb begin
    foo = bar;
    foo[0] = 0;
    foo[1] = 0;
    foo[2] = 0;
    foo[a] = 0;
    foo[a+:1] = '{0};
    foo[a-:2] = '{0, 0};
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 2));
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(2, 2));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[2]") == ConstantRange(0, 0));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 2));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 2));
    CHECK(getBitRange(netlist, "foo[a-:2]") == ConstantRange(0, 2));
}

TEST_CASE("Unpacked 2D array element and range") {
    auto tree = SyntaxTree::fromText(R"(
module m (input int a);
  logic foo [3:0] [1:0];
  logic bar [1:0];
  always_comb begin
    foo[0] = bar;
    foo[1] = bar;
    foo[2] = bar;
    foo[3] = bar;
    foo[0][1] = 0;
    foo[1][1] = 0;
    foo[2][1] = 0;
    foo[3][1] = 0;
    foo[a] = bar;
    foo[a][1] = 0;
    foo[a][a] = 0;
    foo[a+:1] = '{'{0, 0}};
    foo[a-:2] = '{'{0, 0}, '{0, 0}};
    foo[1][a] = 0;
    foo[1][a+:1] = '{0};
    foo[1][a-:2] = '{0, 0};
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(6, 7));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(4, 5));
    CHECK(getBitRange(netlist, "foo[2]") == ConstantRange(2, 3));
    CHECK(getBitRange(netlist, "foo[3]") == ConstantRange(0, 1));
    CHECK(getBitRange(netlist, "foo[0][1]") == ConstantRange(6, 6));
    CHECK(getBitRange(netlist, "foo[1][1]") == ConstantRange(4, 4));
    CHECK(getBitRange(netlist, "foo[2][1]") == ConstantRange(2, 2));
    CHECK(getBitRange(netlist, "foo[3][1]") == ConstantRange(0, 0));
    // Dynamic indices.
    CHECK(getBitRange(netlist, "foo[a]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a][1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a][a]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a+:1]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[a-:2]") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[1][a]") == ConstantRange(4, 5));
    CHECK(getBitRange(netlist, "foo[1][a+:1]") == ConstantRange(4, 5));
    CHECK(getBitRange(netlist, "foo[1][a-:2]") == ConstantRange(4, 5));
}

//===---------------------------------------------------------------------===//
// Struct, union and enum selectors.
//===---------------------------------------------------------------------===//

TEST_CASE("Struct member") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  struct packed {
    logic a;
    int b;
    longint c;
  } foo;
  always_comb begin
    foo = 0;
    foo.a = 0;
    foo.b = 0;
    foo.c = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 96));
    CHECK(getBitRange(netlist, "foo.a") == ConstantRange(96, 96));
    CHECK(getBitRange(netlist, "foo.b") == ConstantRange(64, 95));
    CHECK(getBitRange(netlist, "foo.c") == ConstantRange(0, 63));
}

TEST_CASE("Union member") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  union packed {
    int a, b, c;
  } foo;
  always_comb begin
    foo = 0;
    foo.a = 0;
    foo.b = 0;
    foo.c = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo.a") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo.b") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo.c") == ConstantRange(0, 31));
}

TEST_CASE("Enum member") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  typedef enum logic [7:0] { A, B, C } foo_t;
  foo_t foo;
  assign foo = A;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 7));
}

//===---------------------------------------------------------------------===//
// Combine selection of types with arrays, structs, unions and enums.
//===---------------------------------------------------------------------===//

TEST_CASE("Struct with packed array members") {
    // Test recursion from packed struct.
    auto tree = SyntaxTree::fromText(R"(
module m;
  struct packed {
    logic [3:0] a, b;
  } foo;
  always_comb begin
    foo = 0;
    foo[1] = 0;
    foo[5:1] = 0;
    foo.a[2:1] = 0;
    foo.b[2:1] = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 7));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo[5:1]") == ConstantRange(1, 5));
    CHECK(getBitRange(netlist, "foo.a[2:1]") == ConstantRange(5, 6));
    CHECK(getBitRange(netlist, "foo.b[2:1]") == ConstantRange(1, 2));
}

TEST_CASE("Packed struct with packed union and enum members") {
    // Test recursion from packed struct.
    auto tree = SyntaxTree::fromText(R"(
module m;
  typedef enum int { A, B, C } enum_t;
  struct packed {
    union packed {
      logic [3:0] a, b;
    } u;
    enum_t c;
  } foo;
  always_comb begin
    foo = 0;
    foo[1] = 0;
    foo.u = 0;
    foo.u[2:1] = 0;
    foo.u.a[2:1] = 0;
    foo.u.b[2:1] = 0;
    foo.c = A;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 35));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(1, 1));
    CHECK(getBitRange(netlist, "foo.u") == ConstantRange(32, 35));
    CHECK(getBitRange(netlist, "foo.u[2:1]") == ConstantRange(33, 34));
    CHECK(getBitRange(netlist, "foo.u.a[2:1]") == ConstantRange(33, 34));
    CHECK(getBitRange(netlist, "foo.u.b[2:1]") == ConstantRange(33, 34));
    CHECK(getBitRange(netlist, "foo.c") == ConstantRange(0, 31));
}

TEST_CASE("Packed arrays of structs etc") {
    // Test recursion from packed packed array, packed struct, packed union.
    auto tree = SyntaxTree::fromText(R"(
module m;
  typedef enum int { A, B, C } enum_t;
  typedef struct packed {
    union packed {
      logic [3:0] a, b;
    } u;
    logic [1:0] c;
    enum_t d;
  } foo_t;
  foo_t [3:0] [1:0] foo;
  always_comb begin
    foo = 0;
    foo[0] = 0;
    foo[1] = 0;
    foo[0][0] = 0;
    foo[0][1] = 0;
    foo[0][0].u.a = 0;
    foo[0][1].u.a = 0;
    foo[0][0].u.b = 0;
    foo[0][1].u.b = 0;
    foo[0][0].c = 0;
    foo[0][1].c = 0;
    foo[0][0].d = A;
    foo[0][1].d = A;
    foo[3][1] = 0;
    foo[3][1].u.a = 0;
    foo[3][1].u.b = 0;
    foo[3][1].c = 0;
    foo[3][1].d = A;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 303));
    CHECK(getBitRange(netlist, "foo[0]") == ConstantRange(0, 75));
    CHECK(getBitRange(netlist, "foo[1]") == ConstantRange(76, 151));
    CHECK(getBitRange(netlist, "foo[0][0]") == ConstantRange(0, 37));
    CHECK(getBitRange(netlist, "foo[0][1]") == ConstantRange(38, 75));
    CHECK(getBitRange(netlist, "foo[0][0].u.a") == ConstantRange(34, 37));
    CHECK(getBitRange(netlist, "foo[0][1].u.a") == ConstantRange(72, 75));
    CHECK(getBitRange(netlist, "foo[0][0].u.b") == ConstantRange(34, 37));
    CHECK(getBitRange(netlist, "foo[0][1].u.b") == ConstantRange(72, 75));
    CHECK(getBitRange(netlist, "foo[0][0].c") == ConstantRange(32, 33));
    CHECK(getBitRange(netlist, "foo[0][1].c") == ConstantRange(70, 71));
    CHECK(getBitRange(netlist, "foo[0][0].d") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo[0][1].d") == ConstantRange(38, 69));
    CHECK(getBitRange(netlist, "foo[3][1]") == ConstantRange(266, 303));
    CHECK(getBitRange(netlist, "foo[3][1].u.a") == ConstantRange(300, 303));
    CHECK(getBitRange(netlist, "foo[3][1].u.b") == ConstantRange(300, 303));
    CHECK(getBitRange(netlist, "foo[3][1].c") == ConstantRange(298, 299));
    CHECK(getBitRange(netlist, "foo[3][1].d") == ConstantRange(266, 297));
}

TEST_CASE("Union with packed struct members") {
    // Test recursion from packed union, packed struct.
    auto tree = SyntaxTree::fromText(R"(
module m;
  typedef enum int { A, B, C } enum_t;
  union packed {
    struct packed {
      logic [3:0] a, b;
    } x, y;
  } [3:0] foo;
  always_comb begin
    foo = 0;
    foo[0].x.a = 0;
    foo[0].x.b = 0;
    foo[0].y.a = 0;
    foo[0].y.b = 0;
    foo[3].x.a = 0;
    foo[3].x.b = 0;
    foo[3].y.a = 0;
    foo[3].y.b = 0;
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(getBitRange(netlist, "foo") == ConstantRange(0, 31));
    CHECK(getBitRange(netlist, "foo[0].x.a") == ConstantRange(4, 7));
    CHECK(getBitRange(netlist, "foo[0].x.b") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[0].y.a") == ConstantRange(4, 7));
    CHECK(getBitRange(netlist, "foo[0].y.b") == ConstantRange(0, 3));
    CHECK(getBitRange(netlist, "foo[3].x.a") == ConstantRange(28, 31));
    CHECK(getBitRange(netlist, "foo[3].x.b") == ConstantRange(24, 27));
    CHECK(getBitRange(netlist, "foo[3].y.a") == ConstantRange(28, 31));
    CHECK(getBitRange(netlist, "foo[3].y.b") == ConstantRange(24, 27));
}
