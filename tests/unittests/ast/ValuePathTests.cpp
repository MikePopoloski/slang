// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/EvalContext.h"
#include "slang/ast/ValuePath.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"

static std::string pathStr(Compilation& compilation, std::string_view instPath) {
    auto& inst = compilation.getRoot().lookupName<InstanceSymbol>(instPath);
    EvalContext evalCtx(inst);
    return ValuePath(*inst.getPortConnections()[0]->getExpression(), evalCtx).toString(evalCtx);
}

TEST_CASE("ValuePath toString - named value") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a); endmodule
module top;
    logic a;
    m inst(.a(a));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a");
}

TEST_CASE("ValuePath toString - element select constant index") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a); endmodule
module top;
    logic [7:0] a;
    m inst(.a(a[2]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[2]");
}

TEST_CASE("ValuePath toString - element select dynamic index") {
    // A non-constant selector falls through to the recursive doStringify path.
    auto tree = SyntaxTree::fromText(R"(
module m(input logic a); endmodule
module top;
    logic [7:0] a;
    logic [2:0] i;
    m inst(.a(a[i]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[i]");
}

TEST_CASE("ValuePath toString - range select constant simple colon") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [2:0] a); endmodule
module top;
    logic [7:0] a;
    m inst(.a(a[3:1]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[3:1]");
}

TEST_CASE("ValuePath toString - range select constant indexed ascending") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [2:0] a); endmodule
module top;
    logic [7:0] a;
    m inst(.a(a[1+:3]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[1+:3]");
}

TEST_CASE("ValuePath toString - range select constant indexed descending") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [2:0] a); endmodule
module top;
    logic [7:0] a;
    m inst(.a(a[3-:3]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[3-:3]");
}

TEST_CASE("ValuePath toString - range select dynamic left operand") {
    // When left cannot be evaluated, doStringify recurses on both operands.
    // The literal right operand exercises the default/syntax fallback.
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [2:0] a); endmodule
module top;
    logic [7:0] a;
    logic [2:0] i;
    m inst(.a(a[i+:3]));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "a[i+:3]");
}

TEST_CASE("ValuePath toString - struct member access") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [3:0] a); endmodule
module top;
    typedef struct packed { logic [3:0] x; logic [3:0] y; } pt;
    pt s;
    m inst(.a(s.x));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "s.x");
}

TEST_CASE("ValuePath toString - static class member access") {
    // Static class properties format as "Type::member" instead of "obj.member".
    auto tree = SyntaxTree::fromText(R"(
class Foo;
    static logic [3:0] prop;
endclass
module m(input logic [3:0] a); endmodule
module top;
    Foo obj;
    m inst(.a(obj.prop));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "Foo::prop");
}

TEST_CASE("ValuePath toString - concatenation") {
    auto tree = SyntaxTree::fromText(R"(
module m(input logic [7:0] a); endmodule
module top;
    logic [3:0] a, b;
    m inst(.a({a, b}));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "{a, b}");
}

TEST_CASE("ValuePath toString - function call") {
    auto tree = SyntaxTree::fromText(R"(
function automatic logic [3:0] foo(input logic [3:0] x);
    return x;
endfunction
module m(input logic [3:0] a); endmodule
module top;
    logic [3:0] a;
    m inst(.a(foo(a)));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "foo(a)");
}

TEST_CASE("ValuePath toString - function call with no arguments") {
    auto tree = SyntaxTree::fromText(R"(
function automatic logic [3:0] bar();
    return 4'hA;
endfunction
module m(input logic [3:0] a); endmodule
module top;
    m inst(.a(bar()));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    CHECK(pathStr(compilation, "top.inst") == "bar()");
}
