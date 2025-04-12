// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/parsing/Parser.h"
#include "slang/syntax/AllSyntax.h"

TEST_CASE("Evaluate assignment expression") {
    // Evaluate an assignment expression (has an LValue we can observe)
    auto syntax = SyntaxTree::fromText("i = i + 3");

    // Fabricate a symbol for the `i` variable
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto varToken = syntax->root().getFirstToken();
    VariableSymbol local{varToken.valueText(), varToken.location(), VariableLifetime::Automatic};
    local.setType(compilation.getIntType());

    // Bind the expression tree to the symbol
    scope.addMember(local);

    ASTContext astCtx(scope, LookupLocation::max);
    auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(), astCtx,
                                   ASTFlags::AssignmentAllowed);
    REQUIRE(syntax->diagnostics().empty());

    // Initialize `i` to 1.
    EvalContext evalCtx(astCtx);
    evalCtx.pushEmptyFrame();

    auto i = evalCtx.createLocal(&local, SVInt(32, 1, true));

    // Evaluate the expression tree.
    bound.eval(evalCtx);
    CHECK(i->integer() == 4);

    // Run it again, results should be as you'd expect
    bound.eval(evalCtx);
    CHECK(i->integer() == 7);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation") {
    // Assignment operator should increase RHS size to 20
    auto syntax = SyntaxTree::fromText("i = 5'b0101 + 4'b1100");

    // Fabricate a symbol for the `i` variable
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto varToken = syntax->root().getFirstToken();
    VariableSymbol local{varToken.valueText(), varToken.location(), VariableLifetime::Automatic};
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                   ASTContext(scope, LookupLocation::max),
                                   ASTFlags::AssignmentAllowed);

    REQUIRE(syntax->diagnostics().empty());

    CHECK(bound.type->getBitWidth() == 20);
    const Expression& rhs = bound.as<AssignmentExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);
    const Expression& op1 = rhs.as<BinaryExpression>().left();
    CHECK(op1.type->getBitWidth() == 20);
    const Expression& op2 = rhs.as<BinaryExpression>().right();
    CHECK(op2.type->getBitWidth() == 20);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation 2") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 4'b1100) == 21'b1)");
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax->root().getFirstToken();
    VariableSymbol local{varToken.valueText(), varToken.location(), VariableLifetime::Automatic};
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                   ASTContext(scope, LookupLocation::max),
                                   ASTFlags::AssignmentAllowed);
    REQUIRE(syntax->diagnostics().empty());

    CHECK(bound.type->getBitWidth() == 20);
    const Expression& rhs = bound.as<AssignmentExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);

    const Expression& rrhs =
        rhs.as<BinaryExpression>().right().as<ConversionExpression>().operand();
    CHECK(rrhs.type->getBitWidth() == 1);

    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const Expression& shiftExpr = op1.as<BinaryExpression>().left();
    CHECK(shiftExpr.type->getBitWidth() == 21);
    CHECK(op1.type->getBitWidth() == 21);
    const Expression& op2 = rrhs.as<BinaryExpression>().right();
    CHECK(op2.type->getBitWidth() == 21);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation real") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 2.0) == 21'b1)");
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax->root().getFirstToken();
    VariableSymbol local{varToken.valueText(), varToken.location(), VariableLifetime::Automatic};
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                   ASTContext(scope, LookupLocation::max),
                                   ASTFlags::AssignmentAllowed);
    REQUIRE(syntax->diagnostics().empty());
    CHECK(bound.type->getBitWidth() == 20);

    const Expression& rhs = bound.as<AssignmentExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);

    const Expression& rrhs =
        rhs.as<BinaryExpression>().right().as<ConversionExpression>().operand();
    CHECK(rrhs.type->getBitWidth() == 1);

    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const ConversionExpression& convExpr =
        op1.as<BinaryExpression>().left().as<ConversionExpression>();
    CHECK(convExpr.type->getBitWidth() == 64);
    CHECK(convExpr.type->isFloating());

    const Expression& shiftExpr = convExpr.operand();
    CHECK(shiftExpr.type->getBitWidth() == 17);
    CHECK(shiftExpr.type->isIntegral());

    const Expression& rshiftOp = shiftExpr.as<BinaryExpression>().right();
    CHECK(rshiftOp.type->getBitWidth() == 1);

    const Expression& lshiftOp = shiftExpr.as<BinaryExpression>().left();
    CHECK(lshiftOp.type->getBitWidth() == 17);
    CHECK(op1.type->getBitWidth() == 64);
    CHECK(op1.type->isFloating());

    const Expression& op2 = rrhs.as<BinaryExpression>().right();
    CHECK(op2.type->getBitWidth() == 64);
    CHECK(op2.type->isFloating());
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Expression types") {
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        scope.getCompilation().addSyntaxTree(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type->toString();
    };

    declare("logic [7:0] l;");
    declare("logic signed [7:0] sl;");
    declare("logic signed [2:0][7:0] sla;");
    declare("logic [7:0][3:2] pa;");
    declare("bit [2:10] b1;");
    declare("int i;");
    declare("integer ig4;");
    declare("real r;");
    declare("shortreal sr;");
    declare("struct packed { logic a; bit b; } sp;");
    declare("union packed { logic [1:0] a; bit [0:1] b; } up;");
    declare("struct { logic a; bit b; } su;");
    declare("struct { bit a; bit b; } su2;");
    declare("reg reg1, reg2;");
    declare("enum {EVAL1, EVAL2} e1;");

    // Literals / misc
    CHECK(typeof("\"asdfg\"") == "bit[39:0]");
    CHECK(typeof("reg1 + reg2") == "reg");
    CHECK(typeof("e1") == "enum{EVAL1=32'sd0,EVAL2=32'sd1}e$1");
    CHECK(typeof("10.234ns") == "realtime");

    // Unary operators
    CHECK(typeof("+i") == "int");
    CHECK(typeof("-sp") == "struct packed{logic a;bit b;}s$1");
    CHECK(typeof("!r") == "bit");
    CHECK(typeof("~l") == "logic[7:0]");
    CHECK(typeof("~r") == "<error>");
    CHECK(typeof("&l") == "logic");
    CHECK(typeof("~^b1") == "bit");

    // Binary operators
    CHECK(typeof("l + pa") == "logic[15:0]");
    CHECK(typeof("sl - pa") == "logic[15:0]");
    CHECK(typeof("sl * 16'sd5") == "logic signed[15:0]"); // both signed, result is signed
    CHECK(typeof("b1 * i") == "bit[31:0]");               // 2 state result
    CHECK(typeof("b1 / i") == "logic[31:0]");             // divide always produces 4 state
    CHECK(typeof("b1 % i") == "logic[31:0]");             // mod always produces 4 state
    CHECK(typeof("b1 ** (9234'd234)") == "logic[8:0]");   // self determined from lhs
    CHECK(typeof("r + sr") == "real");
    CHECK(typeof("sr + sr") == "shortreal");
    CHECK(typeof("l + r") == "real");
    CHECK(typeof("l + sr") == "shortreal");
    CHECK(typeof("sp < r") == "logic");
    CHECK(typeof("su < r") == "<error>");
    CHECK(typeof("pa <<< b1") == "logic[7:0][3:2]");
    CHECK(typeof("b1 >> b1") == "bit[2:10]");
    CHECK(typeof("b1 >> sl") == "logic[8:0]");
    CHECK(typeof("sp == l") == "logic");
    CHECK(typeof("b1 == b1") == "bit");
    CHECK(typeof("b1 != l") == "logic");
    CHECK(typeof("b1 === b1") == "bit");
    CHECK(typeof("b1 !== l") == "bit");
    CHECK(typeof("r == b1") == "bit");
    CHECK(typeof("b1 == r") == "bit");
    CHECK(typeof("l == r") == "logic");
    CHECK(typeof("su == su") == "logic");
    CHECK(typeof("su2 == su2") == "bit");
    CHECK(typeof("EVAL1 + 5") == "int");
    CHECK(typeof("up + 5") == "logic[31:0]");
    CHECK(typeof("up + up") == "union packed{logic[1:0] a;bit[0:1] b;}u$1");

    // Unpacked arrays
    declare("bit [7:0] arr1 [2];");
    declare("bit [7:0] arr2 [2:0];");
    declare("bit [7:0] arr3 [3];");
    declare("logic signed [7:0] arr4 [3];");
    CHECK(typeof("arr1 == arr2") == "<error>");
    CHECK(typeof("arr2 == arr3") == "bit");
    CHECK(typeof("arr2 == arr4") == "<error>");

    // Dynamic arrays
    declare("bit [7:0] dar1 [];");
    declare("bit [0:7] dar2 [];");
    CHECK(typeof("dar1 == dar2") == "bit");
    CHECK(typeof("dar1 != dar2") == "bit");
    CHECK(typeof("dar1 != arr1") == "<error>");
    CHECK(typeof("dar1[3]") == "bit[7:0]");
    CHECK(typeof("dar2[i]") == "bit[0:7]");
    CHECK(typeof("dar1[2:3]") == "bit[7:0]$[2:3]");
    CHECK(typeof("dar1[2+:3]") == "bit[7:0]$[0:2]");
    CHECK(typeof("dar1[2-:5]") == "bit[7:0]$[0:4]");

    // Associative arrays
    declare("bit [7:0] aar1 [int];");
    declare("bit [0:7] aar2 [int];");
    declare("bit [0:7] aar3 [*];");
    CHECK(typeof("aar1 == aar2") == "bit");
    CHECK(typeof("aar1 != aar3") == "<error>");

    // Queues
    declare("bit [7:0] q1 [$];");
    declare("bit [0:7] q2 [$];");
    declare("bit [0:7] q3 [$:200];");
    CHECK(typeof("q1 == q2") == "bit");
    CHECK(typeof("q1 != q3") == "bit");

    // Conditional operator
    CHECK(typeof("i ? l : pa") == "logic[15:0]");
    CHECK(typeof("r ? b1 : i") == "bit[31:0]");
    CHECK(typeof("i ? arr2 : arr3") == "bit[7:0]$[2:0]");
    CHECK(typeof("i ? dar1 : dar2") == "bit[7:0]$[]");
    CHECK(typeof("i ? arr1: arr2") == "<error>");
    CHECK(typeof("arr2 ? 1 : 0") == "<error>");
    CHECK(typeof("i ? EVAL1 : EVAL2") == "enum{EVAL1=32'sd0,EVAL2=32'sd1}e$1");
    CHECK(typeof("b1 ? e1 : e1") == "enum{EVAL1=32'sd0,EVAL2=32'sd1}e$1");
    CHECK(typeof("ig4 ? e1 : EVAL1") == "enum{EVAL1=32'sd0,EVAL2=32'sd1}e$1");

    // Member access
    declare("struct packed { logic [13:0] a; bit b; } foo;");
    declare("struct packed { logic [13:0] a; bit b; } [3:0] spPackedArray;");
    declare("union { logic [13:0] a; int b; } upUnion;");
    CHECK(typeof("foo.a") == "logic[13:0]");
    CHECK(typeof("spPackedArray") == "struct packed{logic[13:0] a;bit b;}s$5[3:0]");
    CHECK(typeof("spPackedArray[0].a") == "logic[13:0]");
    CHECK(typeof("upUnion.a") == "logic[13:0]");
    CHECK(typeof("upUnion.b") == "int");

    // Selections
    CHECK(typeof("l[0:0]") == "logic[0:0]");
    CHECK(typeof("b1[2:2]") == "bit[2:2]");
    CHECK(typeof("sl[7:0]") == "logic[7:0]");
    CHECK(typeof("sla[0]") == "logic[7:0]");
    CHECK(typeof("arr4[0]") == "logic signed[7:0]");

    // Casts
    declare("parameter int FOO = 1;");
    CHECK(typeof("(FOO + 2)'(b1)") == "bit[2:0]");
    CHECK(typeof("int'(b1)") == "int");
    CHECK(typeof("5'(sp)") == "logic[4:0]");
    CHECK(typeof("signed'(b1)") == "bit signed[8:0]");
    CHECK(typeof("unsigned'(b1)") == "bit[8:0]");
    CHECK(typeof("signed'(sl)") == "logic signed[7:0]");
    CHECK(typeof("unsigned'(sl)") == "logic[7:0]");
    CHECK(typeof("const'(sp)") == "struct packed{logic a;bit b;}s$1");
    CHECK(typeof("const'(FOO)") == "int");
    CHECK(typeof("const'(r)") == "real");

    // Strings
    declare("string s1 = \"asdf\";");
    declare("string s2 = \"asdf\" | 1;");
    declare("string s3 = 1 ? \"asdf\" : \"bar\";");
    declare("string s4 = {\"asdf\", 8'd42};");

    // Inside expressions
    CHECK(typeof("i inside { 4, arr3, pa, sp, dar1 }") == "logic");

    // Min-typ-max
    CHECK(typeof("(arr1[99]:3'd4:99'd4) + 2'd1") == "bit[2:0]");

    // Unpacked unions
    declare("union { int i; real r; } uu1, uu2;");
    CHECK(typeof("uu1 == uu2") == "bit");
    CHECK(typeof("uu1 !== uu2") == "bit");
    CHECK(typeof("1 ? uu1 : uu2") == "union{int i;real r;}u$3");

    auto diags = filterWarnings(compilation.getAllDiagnostics());
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::BadUnaryExpression);
    CHECK(diags[1].code == diag::BadBinaryExpression);
    CHECK(diags[2].code == diag::BadBinaryExpression);
    CHECK(diags[3].code == diag::BadBinaryExpression);
    CHECK(diags[4].code == diag::BadBinaryExpression);
    CHECK(diags[5].code == diag::BadBinaryExpression);
    CHECK(diags[6].code == diag::BadConditionalExpression);
    CHECK(diags[7].code == diag::NotBooleanConvertible);
}

TEST_CASE("Expression - bad name references") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    typedef struct { logic f; } T;

    int i = T + 2;      // not a value
    int j = (3 + 4)(2); // not callable
    int k = i(2);       // not a task or function

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::NotAValue);
    CHECK(diags[1].code == diag::ExpressionNotCallable);
    CHECK(diags[2].code == diag::ExpressionNotCallable);
}

TEST_CASE("Expression - bad use of data type") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    typedef int blah;

    int i = int;
    int j = -(int + 1);
    int k = (blah * 2);
    int l = $bits(blah & 2);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExpectedExpression);
    CHECK(diags[1].code == diag::ExpectedExpression);
    CHECK(diags[2].code == diag::NotAValue);
    CHECK(diags[3].code == diag::NotAValue);
}

TEST_CASE("Expression - allowed data type") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    typedef int blah;

    int i = $bits(blah);
    int j = $bits(logic[3:0]);
    string s = $typename(blah);
    string t = $typename(logic[3:0]);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("$bits / typename - hierarchical allowed in non-const") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    int i = $bits(n.asdf);
    string s = $typename(n.asdf);
endmodule

module n;
    logic [5:1] asdf;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checking for required constant subexpressions") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    int a;
    function int foo;
        return a;
    endfunction

    logic [3:0] asdf;
    always_comb asdf = asdf[foo():0];
    always_comb asdf = asdf[0+:foo()];
    always_comb asdf = {foo() {32'd1}};
    always_comb asdf = foo()'(1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
}

TEST_CASE("Invalid string conversions") {
    auto tree = SyntaxTree::fromText(R"(
module m1;

    string s;

    typedef logic[15:0] r_t;
    r_t r;

    always_comb begin
        s = r;
        r = s;
        r = r_t'(s);    // ok
        s = string'(r); // ok
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NoImplicitConversion);
    CHECK(diags[1].code == diag::NoImplicitConversion);
}

TEST_CASE("Integer literal corner cases") {
    auto tree = SyntaxTree::fromText(R"(
`define FOO aa_ff
`define BAR 'h

module m1;

    int i = 35'd123498234978234;
    int j = 0'd234;
    int k = 16777216'd1;
    int l = 16   `BAR `FOO;
    integer m = 'b ??0101?1;
    int n = 999999999999;
    int o = 'b _?1;
    int p = 'b3;
    int q = 'ox789;
    int r = 'd?;
    int s = 'd  z_;
    int t = 'd x1;
    int u = 'd a;
    int v = 'h g;
    int w = 3'h f;
    int x = 'd;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:7:11: warning: implicit conversion from 'bit[34:0]' to 'int' changes value from 35'h22c6d1fba to 745349050 [-Wconstant-conversion]
    int i = 35'd123498234978234;
          ^ ~~~~~~~~~~~~~~~~~~~
source:7:17: warning: vector literal too large for the given number of bits (47 bits needed) [-Wvector-overflow]
    int i = 35'd123498234978234;
                ^
source:8:13: error: size of vector literal cannot be zero
    int j = 0'd234;
            ^
source:9:13: error: size of vector literal is too large (> 16777215 bits)
    int k = 16777216'd1;
            ^
source:12:13: warning: signed integer literal overflows 32 bits, will be truncated to -727379969 [-Wint-overflow]
    int n = 999999999999;
            ^
source:13:16: error: numeric literals must not start with a leading underscore
    int o = 'b _?1;
               ^
source:14:15: error: expected binary digit
    int p = 'b3;
              ^
source:15:17: error: expected octal digit
    int q = 'ox789;
                ^
source:18:17: error: decimal literals cannot have multiple digits if at least one of them is X or Z
    int t = 'd x1;
                ^
source:19:16: error: expected decimal digit
    int u = 'd a;
               ^
source:20:16: error: expected hexadecimal digit
    int v = 'h g;
               ^
source:21:17: warning: vector literal too large for the given number of bits (4 bits needed) [-Wvector-overflow]
    int w = 3'h f;
                ^
source:22:15: error: expected vector literal digits
    int x = 'd;
              ^
)");
}

TEST_CASE("Real literal corner cases") {
    auto tree = SyntaxTree::fromText(R"(
module m1;
    real a = 9999e99999;
    real b = 9999e-99999;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:3:14: warning: value of real literal is too large; maximum is 1.79769e+308 [-Wreal-overflow]
    real a = 9999e99999;
             ^
source:4:14: warning: value of real literal is too small; minimum is 4.94066e-324 [-Wreal-underflow]
    real b = 9999e-99999;
             ^
)");
}

#ifdef CI_BUILD
TEST_CASE("Crazy long hex literal") {
    std::string str = "int i = 'h";
    str += std::string(4194304, 'f');
    str += ';';

    auto tree = SyntaxTree::fromText(str);

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::LiteralSizeTooLarge);
}
#endif

TEST_CASE("Simple assignment patterns") {
    auto tree = SyntaxTree::fromText(R"(
module n(input int frob[3]);
endmodule

module m;

    parameter int foo[2] = '{42, -39};
    parameter struct { int a; logic [1:0] b; } asdf = '{999, '{1, 0}};

    typedef struct { int a; int b; int c; } type_t;
    parameter bar = type_t '{1, 2, 3};

    type_t baz;
    initial baz = '{1, 2, 3};

    n n1('{1, 2, 3});

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.foo");
    auto elems = foo.getValue().elements();
    REQUIRE(elems.size() == 2);
    CHECK(elems[0].integer() == 42);
    CHECK(elems[1].integer() == -39);

    auto& asdf = compilation.getRoot().lookupName<ParameterSymbol>("m.asdf");
    elems = asdf.getValue().elements();
    REQUIRE(elems.size() == 2);
    CHECK(elems[0].integer() == 999);
    CHECK(elems[1].integer() == 2);

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.bar");
    elems = bar.getValue().elements();
    REQUIRE(elems.size() == 3);
    CHECK(elems[0].integer() == 1);
    CHECK(elems[1].integer() == 2);
    CHECK(elems[2].integer() == 3);
}

TEST_CASE("Replicated assignment patterns") {
    auto tree = SyntaxTree::fromText(R"(
module n(input int frob[3]);
endmodule

module m;

    parameter int foo[2] = '{2 {42}};
    parameter struct { int a; logic [1:0] b; } asdf = '{2 {2}};

    typedef struct { int a; shortint b; integer c; longint d; } type_t;
    parameter bar = type_t '{2 {1, 2}};

    type_t baz;
    initial baz = '{2 {1, 2}};

    n n1('{3 {2}});

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.foo");
    auto elems = foo.getValue().elements();
    REQUIRE(elems.size() == 2);
    CHECK(elems[0].integer() == 42);
    CHECK(elems[1].integer() == 42);

    auto& asdf = compilation.getRoot().lookupName<ParameterSymbol>("m.asdf");
    elems = asdf.getValue().elements();
    REQUIRE(elems.size() == 2);
    CHECK(elems[0].integer() == 2);
    CHECK(elems[1].integer() == 2);

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.bar");
    elems = bar.getValue().elements();
    REQUIRE(elems.size() == 4);
    CHECK(elems[0].integer() == 1);
    CHECK(elems[1].integer() == 2);
    CHECK(elems[2].integer() == 1);
    CHECK(elems[3].integer() == 2);
}

TEST_CASE("Structured assignment patterns") {
    auto tree = SyntaxTree::fromText(R"(
module n(input int frob[3]);
endmodule

module m;

    typedef struct { int a; shortint b; integer c; longint d; logic [1:0] e; } type_t;
    parameter type_t bar = '{ c:9, default:2, int:42, int:37, d:-1 };

    parameter int index = 1 * 2 - 1;
    parameter int foo[3] = '{ default:0, int:1, index - 1 + 1:-42 };

    type_t baz;
    initial baz = '{ c:9, default:2, int:42, int:37, d:-1 };

    n n1('{ default:0, int:1, index - 1 + 1:-42 });

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().lookupName<ParameterSymbol>("m.bar");
    auto elems = bar.getValue().elements();
    REQUIRE(elems.size() == 5);
    CHECK(elems[0].integer() == 37);
    CHECK(elems[1].integer() == 2);
    CHECK(elems[2].integer() == 9);
    CHECK(elems[3].integer() == -1);
    CHECK(elems[4].integer() == 2);

    auto& foo = compilation.getRoot().lookupName<ParameterSymbol>("m.foo");
    elems = foo.getValue().elements();
    REQUIRE(elems.size() == 3);
    CHECK(elems[0].integer() == 1);
    CHECK(elems[1].integer() == -42);
    CHECK(elems[2].integer() == 1);
}

TEST_CASE("Array select out of bounds - valid") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam logic[3:0][31:0] foo = '{default:0};
    localparam int n = -1;

    localparam int j = n >= 0 ? foo[n] : -4;
    int k = n >= 0 ? foo[n] : -4;

    localparam logic[1:0][31:0] l = n >= 0 ? foo[1:n] : '0;
    logic[1:0][31:0] o = n >= 0 ? foo[1:n] : '0;

    localparam logic[1:0][31:0] p = n >= 0 ? foo[n+:2] : '0;
    logic[1:0][31:0] q = n >= 0 ? foo[n+:2] : '0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Array select out of bounds - invalid") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam logic[3:0][31:0] foo = '{default:0};
    localparam int n = -1;

    localparam int j = n >= -2 ? foo[n] : -4;
    int k = n >= -2 ? foo[n] : -4;

    localparam logic[1:0][31:0] l = n >= -2 ? foo[1:n] : '0;
    logic[1:0][31:0] o = n >= -2 ? foo[1:n] : '0;

    localparam logic[1:0][31:0] p = n >= -2 ? foo[n+:2] : '0;
    logic[1:0][31:0] q = n >= -2 ? foo[n+:2] : '0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::IndexOOB);
    CHECK(diags[1].code == diag::IndexOOB);
    CHECK(diags[2].code == diag::RangeOOB);
    CHECK(diags[3].code == diag::RangeOOB);
    CHECK(diags[4].code == diag::RangeOOB);
    CHECK(diags[5].code == diag::RangeOOB);
}

TEST_CASE("Empty concat error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i = {1 {}};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::EmptyConcatNotAllowed);
}

TEST_CASE("Consteval - infinite recursion checking") {
    auto tree = SyntaxTree::fromText(R"(
function int foo;
    return bar() + 1;
endfunction

function int bar;
    return foo();
endfunction

module m;
    localparam int i = foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalExceededMaxCallDepth);
}

TEST_CASE("Consteval - infinite loop checking") {
    auto tree = SyntaxTree::fromText(R"(
function int foo;
    for (int i = 0; i < 10000; i++) begin end
endfunction

module m;
    localparam int i = foo();
endmodule
)");

    // Reduce this a bit just to make the tests faster.
    CompilationOptions co;
    co.maxConstexprSteps = 8192;

    Bag options;
    options.set(co);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalExceededMaxSteps);
}

TEST_CASE("Consteval - enum used in constant function") {
    auto tree = SyntaxTree::fromText(R"(
typedef enum { A, B } e_t;

function int foo;
    return A;
endfunction

module m;
    localparam int i = foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Disallowed assignment contexts") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    int j;
    int p;
    logic [(j = 2) : 0] asdf;
    assign i = 1 + (j = 1);

    initial p = {j = 1};
    initial if (p = 1) begin end

    assign i = i++;
    assign i = ++i;

    // This is ok
    initial p = 1 + (j = 1);

    function func(int k);
    endfunction

    // Initialization in a procedural context is also ok
    initial begin
        automatic int k = 1;
        automatic int l = k++;
        static int m = 2;
        static int n = m++;

        static int foo = k; // disallowed

        func.k = 4; // ok, param is static
    end

    final begin
        p <= 5;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[1].code == diag::AssignmentNotAllowed);
    CHECK(diags[2].code == diag::AssignmentRequiresParens);
    CHECK(diags[3].code == diag::AssignmentRequiresParens);
    CHECK(diags[4].code == diag::IncDecNotAllowed);
    CHECK(diags[5].code == diag::IncDecNotAllowed);
    CHECK(diags[6].code == diag::AutoFromStaticInit);
    CHECK(diags[7].code == diag::NonblockingInFinal);
}

TEST_CASE("Assignment error checking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum { ASD = 2 } asdf;
    localparam int i[3] = '{1, 0, ASD};
    const struct { int j = i[0] + 2; } foo = '{3};

    initial begin
        ASD = ASD;
        i[0] = 4;
        foo.j = 5;
    end

    always begin
        automatic int i;
        i <= 1;
    end

    logic o,p;
    assign {o,p}[0] = 1;
    assign {o,p}[1:0] = 2'd1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::CantModifyConst);
    CHECK(diags[1].code == diag::CantModifyConst);
    CHECK(diags[2].code == diag::AssignmentToConstVar);
    CHECK(diags[3].code == diag::NonblockingAssignmentToAuto);
    CHECK(diags[4].code == diag::ExpressionNotAssignable);
    CHECK(diags[5].code == diag::ExpressionNotAssignable);
}

TEST_CASE("Subroutine calls with out params from various contexts") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    // These are all fine
    initial begin
        automatic int i = 1;
        automatic int j = mutate(i);
        static int k = 2;
        static int l = mutate(k);
        void'(mutate(j));
        void'(mutate(k));
    end

    int i = 0;
    int j = mutate(i);

    function int mutate(output int f);
        f++;
        return f - 1;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type operator") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [3:0] a = 0;
    logic [4:0] b = 1;
    var type(5'(a) + b) foo = 5'(a) + b;
    int i = type(int)'(a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Time literal + units / precision") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    timeunit 1ns / 1ps;
    localparam real r = 234.0567891ns;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& r = compilation.getRoot().lookupName<ParameterSymbol>("m.r");
    CHECK(r.getValue().real() == 234.0567891);
}

TEST_CASE("Fixed / dynamic array assignments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int bar[2] = '{5, 6};
    function automatic int func;
        int foo[] = '{1, 2, 3};
        foo = bar;
        return $size(foo);
    endfunction

    localparam int asdf = func();

    function automatic int func2;
        int bar[3];
        int foo[] = '{1, 2, 3};
        bar = foo;
        return bar[2];
    endfunction

    localparam int asdf2 = func2();

    function automatic int func3;
        int bar[4];
        int foo[] = '{1, 2, 3};
        bar = foo;
        return bar[2];
    endfunction

    localparam int asdf3 = func3();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& asdf = compilation.getRoot().lookupName<ParameterSymbol>("m.asdf");
    CHECK(asdf.getValue().integer() == 2);

    auto& asdf2 = compilation.getRoot().lookupName<ParameterSymbol>("m.asdf2");
    CHECK(asdf2.getValue().integer() == 3);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalDynamicToFixedSize);
}

TEST_CASE("New array expression") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[] = new [3];
    int bar[2];
    initial begin
        foo = new [8] (foo);
        foo = new [9] (bar);
        bar = new [2] (bar); // invalid target
        foo = new [asdf];
        foo = new [3.4];
        foo = new [2] (3.4);
    end

    localparam int i = '{};
    localparam int baz[] = new [i];
    localparam int boz[] = new [3] (baz);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::NewArrayTarget);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::ExprMustBeIntegral);
    CHECK(diags[3].code == diag::BadAssignment);
    CHECK(diags[4].code == diag::EmptyAssignmentPattern);
    CHECK(diags[5].code == diag::WrongNumberAssignmentPatterns);
}

TEST_CASE("Unpacked array concatentions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        typedef int AI3[1:3];
        AI3 A3;
        int AA[int];
        int A9[1:9];
        real R1[][1:9];
        A3 = '{1, 2, 3};
        A9 = '{3{A3}};                  // illegal, A3 is wrong element type
        A9 = '{A3, 4, 5, 6, 7, 8, 9};   // illegal, A3 is wrong element type
        A9 = {A3, 4, 5, A3, 6};         // legal, gives A9='{1,2,3,4,5,1,2,3,6}
        A9 = '{9{1}};                   // legal, gives A9='{1,1,1,1,1,1,1,1,1}
        A9 = {9{32'd1}};                // illegal, no replication in unpacked array concatenation
        A9 = {A3, {4,5,6,7,8,9} };      // illegal, {...} is not self-determined here
        A9 = {A3, '{4,5,6,7,8,9} };     // illegal, '{...} is not self-determined
        A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9}; // legal, A9='{1,2,3,4,5,6,7,8,9}
        AA = {4, 5};                    // illegal, associative arrays
        A9 = {4, 5, R1};                // illegal, bad element type
    end

    initial begin
        typedef int T_QI[$];
        static T_QI jagged_array[$] = '{ {1}, T_QI'{2,3,4}, {5,6} };
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::BadAssignment);
    CHECK(diags[1].code == diag::BadAssignment);
    CHECK(diags[2].code == diag::NoImplicitConversion);
    CHECK(diags[3].code == diag::UnpackedConcatSize);
    CHECK(diags[4].code == diag::ConstantConversion);
    CHECK(diags[5].code == diag::UnsizedInConcat);
    CHECK(diags[6].code == diag::AssignmentPatternNoContext);
    CHECK(diags[7].code == diag::UnpackedConcatAssociative);
    CHECK(diags[8].code == diag::BadConcatExpression);
}

TEST_CASE("Empty array concatenations") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a1 = {};
    int a2[int] = {};
    int a3[2] = {};
    int a4[] = {}; // ok
    int a5[$] = {}; // ok

    int a6 = '{};
    int a7[int] = '{};
    int a8[2] = '{};
    int a9[] = '{}; // ok
    int aa[$] = '{}; // ok
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::EmptyConcatNotAllowed);
    CHECK(diags[1].code == diag::UnpackedConcatAssociative);
    CHECK(diags[2].code == diag::UnpackedConcatSize);
    CHECK(diags[3].code == diag::EmptyAssignmentPattern);
    CHECK(diags[4].code == diag::WrongNumberAssignmentPatterns);
    CHECK(diags[5].code == diag::EmptyAssignmentPattern);
    CHECK(diags[6].code == diag::AssignmentPatternAssociativeType);
    CHECK(diags[7].code == diag::EmptyAssignmentPattern);
    CHECK(diags[8].code == diag::WrongNumberAssignmentPatterns);
    CHECK(diags[9].code == diag::EmptyAssignmentPattern);
    CHECK(diags[10].code == diag::EmptyAssignmentPattern);
}

TEST_CASE("Assignment pattern - invalid default") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i[] = '{default, 5};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExpectedExpression);
}

TEST_CASE("Delay value ambiguity") {
    // This tests ambiguity if delay values are parsed as vectors.
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    initial begin
        i = #3 'd7; // delay 3, assign 32'd7
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Min/typ/max expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int i = (3:4:5);
endmodule
)");

    auto compileVal = [&](auto&& compOptions) {
        Bag options;
        options.set(compOptions);

        Compilation compilation(options);
        compilation.addSyntaxTree(tree);
        NO_COMPILATION_ERRORS;

        return compilation.getRoot().lookupName<ParameterSymbol>("m.i").getValue();
    };

    // Defaults to "Typ"
    CHECK(compileVal(CompilationOptions()).integer() == 4);

    CompilationOptions options;
    options.minTypMax = MinTypMax::Typ;
    CHECK(compileVal(options).integer() == 4);

    options.minTypMax = MinTypMax::Min;
    CHECK(compileVal(options).integer() == 3);

    options.minTypMax = MinTypMax::Max;
    CHECK(compileVal(options).integer() == 5);
}

TEST_CASE("Range select overflow") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [4:0] asdf;
    int i = asdf[2147483647+:2];
    int j = asdf[-2147483647-:3];

    logic [2147483647:2147483646] foo;
    int k = foo[i+:5];

    localparam int l = func1();
    function automatic int func1;
        int a[3];
        int b = 2147483647;
        int c[2] = a[b+:2];
    endfunction

    localparam int n = func2();
    function automatic int func2;
        int a[];
        int b = 2147483647;
        int c[2] = a[b+:2];
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::RangeWidthOverflow);
    CHECK(diags[1].code == diag::RangeWidthOverflow);
    CHECK(diags[2].code == diag::RangeWidthOverflow);
    CHECK(diags[3].code == diag::RangeWidthOverflow);
    CHECK(diags[4].code == diag::RangeWidthOverflow);
}

std::string testStringLiteralsToByteArray(const std::string& text) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(fullText);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    const auto& module = *compilation.getRoot().topInstances[0];
    const ParameterSymbol& param = module.body.memberAt<ParameterSymbol>(0);
    const auto& value = param.getValue();
    std::string result;
    if (value.isUnpacked()) {
        for (const auto& svInt : value.elements()) {
            REQUIRE(svInt.integer().getBitWidth() == 8);
            auto ch = *svInt.integer().as<char>();
            if (!ch)
                break;
            result.push_back(ch);
        }
    }
    else {
        REQUIRE(value.isQueue());
        for (const auto& svInt : *value.queue().get()) {
            REQUIRE(svInt.integer().getBitWidth() == 8);
            auto ch = *svInt.integer().as<char>();
            if (!ch)
                break;
            result.push_back(ch);
        }
    }
    return result;
}

TEST_CASE("String literal assigned to unpacked array of bytes") {
    // Unpacked array size shorter than string literals
    CHECK(testStringLiteralsToByteArray("localparam byte a[3:0] = \"hello world\";") == "hell");
    // Unpacked array size longer than string literals
    CHECK(testStringLiteralsToByteArray("localparam byte a[1:4] = \"hi\";") == "hi");
    // Dynamaic array
    CHECK(testStringLiteralsToByteArray("localparam byte d[] = \"hello world\";") == "hello world");
    // Queue
    CHECK(testStringLiteralsToByteArray("localparam byte q[$] = \"hello world\";") ==
          "hello world");

    // Associative array should fail
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam byte a[string] = "associative";
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

auto testBitstream(const std::string& text, DiagCode code = DiagCode()) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(fullText);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    auto& diags = compilation.getAllDiagnostics();
    if (!diags.empty() && code) {
        if (diags.back().code != code) {
            CHECK(diags.back().code == code);
            FAIL_CHECK(report(diags));
        }
    }

    return diags.size();
}

TEST_CASE("$bits on non-fixed-size array") {
    std::string intBits = "int b = $bits(a);";
    std::string paramBits = "localparam b = $bits(a);";
    std::string types[] = {"string a;",
                           "logic[1:0] a[];",
                           "bit a[$];",
                           "byte a[int];",
                           "struct { string a; int b; } a;",
                           "string a[1:0];",
                           "bit a[1:0][];",
                           "bit a[1:0][$];",
                           "bit a[1:0][int];"};

    std::string typeDef = "typedef ";
    for (const auto& type : types) {
        CHECK(testBitstream(type + intBits) == 0);
        CHECK(testBitstream(type + paramBits) > 0);

        std::string combined = typeDef;
        combined.append(type);
        combined.append(paramBits);
        CHECK(testBitstream(combined, diag::QueryOnDynamicType) == 1);
    }
}

TEST_CASE("bit-stream cast") {
    std::string illegal[] = {
        R"(
// Illegal conversion from 24-bit struct to 32 bit int - compile time error
struct {bit[7:0] a; shortint b;} a;
int b = int'(a);
)",
        R"(
// Illegal conversion from int (32 bits) to struct dest_t (25 or 33 bits), // compile time error
typedef struct {byte a[$]; bit b;} dest_t;
int a;
dest_t b = dest_t'(a);
)",
        R"(
        typedef struct { bit a[int]; int b; } asso;
        asso x = asso'(64'b0);
)"};

    for (const auto& code : illegal) {
        auto count = testBitstream(code, diag::BadConversion);
        if (count != 1) {
            FAIL_CHECK("Bitstream check failed (" << count << "): " << code);
        }
    }

    std::string legal[] = {
        R"(
// Illegal conversion from 20-bit struct to int (32 bits) - run time error
struct {bit a[$]; shortint b;} a = '{{1,0,1,0}, 67};
int b = int'(a);
)",
        R"(
struct {bit[15:0] a; shortint b;} a = '{default:0};
int b = int'(a);
)",
        R"(
typedef struct { shortint address; logic [3:0] code; byte command [2]; } Control;
typedef bit Bits [36:1];
Control p = '{default:0};
Bits stream = Bits'(p);
Control q = Control'(stream);
)",
        R"(
typedef struct { byte length; shortint address; byte payload[]; byte chksum; } Packet;
typedef byte channel_type[$];
Packet genPkt = '{default:0, payload: {1}};
channel_type channel = channel_type'(genPkt);
Packet p = Packet'( channel[0 : 1] );
)"};

    for (const auto& code : legal) {
        auto count = testBitstream(code);
        if (count != 0) {
            FAIL_CHECK("Bitstream check failed (" << count << "): " << code);
        }
    }

    std::string eval[] = {
        R"(
// Illegal conversion from 20-bit struct to int (32 bits) - run time error
localparam struct {bit a[$]; shortint b;} a = '{{1,0,1,0}, 67};
localparam b = int'(a);
)",
        R"(
localparam string str = "hi";
typedef struct { shortint a[]; byte b[-2:-4]; } c;
localparam c d = c'(str);
)",
        R"(
localparam string str = "hello";
typedef struct { shortint a[]; byte b[1:0]; } c;
localparam c d = c'(str);
)"};

    for (const auto& code : eval) {
        auto count = testBitstream(code, diag::ConstEvalBitstreamCastSize);
        if (count != 1) {
            FAIL_CHECK("Bitstream check failed (" << count << "): " << code);
        }
    }

    CHECK(testBitstream("byte a[2]; localparam b = shortint'(a);",
                        diag::ConstEvalNonConstVariable) == 1);
}

TEST_CASE("Streaming operators") {
    struct {
        std::string sv;
        DiagCode msg;
    } illegal[] = {
        {"int a; int b = {>>{a}} + 2;", diag::BadStreamContext},
        {"shortint a,b; int c = {{>>{a}}, b};", diag::BadStreamContext},
        {"int a,b; always_comb {>>{a}} += b;", diag::BadStreamContext},
        {"int a; int b = {<< string {a}};", diag::BadStreamSlice},
        {"typedef bit t[]; int a; int b = {<<t{a}};", diag::BadStreamSlice},
        {"int a, c; int b = {<< c {a}};", diag::ConstEvalNonConstVariable},
        {"int a; int b = {<< 0 {a}};", diag::ValueMustBePositive},
        {"real a; int b = {<< 5 {a}};", diag::BadStreamExprType},
        {"int a; real b = {<< 2 {a}};", diag::BadStreamTargetType},
        {"int a[2]; real b = $itor(a);", diag::BadSystemSubroutineArg},
        {"int a = 0; int b = {>> 4 {a}};", diag::IgnoredSlice},
        {"int a; real b; assign {<< 2 {a}} = b;", diag::BadStreamSourceType},
        {"int a; shortint b; assign {<< 2 {a}} = b;", diag::BadStreamSize},
        {"int a; shortint b; assign b = {<< 4 {a}};", diag::BadStreamSize},
        {"int a; shortint b; assign {>>{b}} = {<< 4 {a}};", diag::BadStreamSize},
        {"int a; real b = real'({<< 4 {a}});", diag::BadStreamCast},
        {"int a; shortint b = shortint'({<< 4 {a}});", diag::BadStreamCast},
        {"typedef struct {byte a[$]; bit b;} dest_t; int a; dest_t b = dest_t'({<<{a}});",
         diag::BadStreamCast},
        {"typedef struct {byte a[$]; bit b;} dest_t;int a;dest_t b;assign {>>{b}}={<<{a}};",
         diag::BadStreamSize},

        {"localparam string s=\"AB\"; localparam byte j= {<<2{s}};", diag::BadStreamSize},
        {"localparam string s=\"AB\"; localparam int j= byte'({<<{s}}) - 5;",
         diag::ConstEvalBitstreamCastSize},
        {"localparam string s=\"AB\"; localparam int j= int'({<<{s}}) - 5;",
         diag::ConstEvalBitstreamCastSize},

        {"int a,b,c; assign {>>{a,b,c}}=23'b1;", diag::BadStreamSize},
        {"int a,b,c; int j={>>{a,b,c}};", diag::BadStreamSize},
        {"int a,b,c; assign {>>{a+b}}=c;", diag::ExpressionNotAssignable},

        {R"(
function int foo(byte bar[]);
    int a;
    {>>{a}} = bar;
    return a;
endfunction
localparam t=foo("AB");
)",
         diag::BadStreamSize},
        {R"(
function int foo(byte bar[]);
    int a;
    {>>{a}} = {<<{bar}};
return a;
endfunction
localparam t=foo("ABCDE");
)",
         diag::BadStreamSize},

        {R"(
    bit [0:2] c [2:0];
    sub u({>>{c}});
endmodule
module sub(output byte b);
)",
         diag::BadStreamSize},

        {R"(
    sub u({>>{2}});
endmodule
module sub(input bit[3:0] a[0:3]);
)",
         diag::BadStreamSize},

        {R"(
    bit [0:1] c [1:0];
    sub u({>>{c}});
endmodule
module sub(inout logic[7:0] b);
            )",
         diag::BadStreamContext},

        {R"(
    byte c [3:0];
    sub u[3:0] ({>>{c}});
endmodule
module sub(input byte b);
)",
         diag::BadStreamContext},
    };

    for (const auto& test : illegal) {
        if (testBitstream(test.sv, test.msg) == 0) {
            FAIL_CHECK(test.sv);
        }
    }

    std::string legal[] = {
        "int a = 0; byte b[4] = {<<3{a}};",
        "int a; byte b[4]; assign {<<3{b}} = a;",
        "int a; byte b[4]; assign {<<3{b}} = {<<5{a}};",
        "byte b[4] = '{default:0}; int a = int'({<<3{b}}) + 5;",
        "shortint a = 0; byte b[2] = '{default:0}; int c = {<<3{a, {<<5{b}}}};",
        "shortint a; byte b[2]; int c; assign {<<3{{<<5{b}}, a}}=c;",
        "struct{bit a[];int b;}a;struct {byte a[];bit b;}b;assign{<<{a}}={>>{b}};",
        "struct{bit a[];int b;}a;int b;assign {>>{a}} = {<<{b}};",
        "localparam int p = {<<{6}}; enum {a={>>{2}},b={<<{p}}, c} t;",

        R"(
    bit [0:1] c [2:0];
    sub u({<<3{shortint'(100)}}, {>>{c}});
endmodule
module sub(input bit[3:0] a[0:3], output byte b);
)"};

    for (const auto& test : legal)
        CHECK(testBitstream(test) == 0);
}

TEST_CASE("Stream expression with") {
    struct {
        std::string sv;
        DiagCode msg;
    } illegal[] = {
        {"byte b[4]; int a = {<<3{b with[]}};", diag::ExpectedExpression},
        {"int a; byte b[4] = {<<3{a with [2]}};", diag::BadStreamWithType},
        {"byte b[4]; int a = {<<3{b with[0.5]}};", diag::ExprMustBeIntegral},
        {"byte b[4] = '{default:0}; int a = {<<3{b with[{65{1'b1}}]}};", diag::IndexOOB},
        {"byte b[4] = '{default:0}; int a = {<<3{b with[4]}};", diag::IndexOOB},
        {"byte b[4]; int a = {<<3{b with[2-:-1]}};", diag::ValueMustBePositive},
        {"byte b[4] = '{default:0}; logic [39:0] a = {<<3{b with[2+:5]}};", diag::RangeOOB},
        {"byte b[3:0] = '{default:0}; int a = {<<3{b with[2+:3]}};", diag::RangeOOB},
        {"byte b[0:3] = '{default:0}; int a = {<<3{b with[2:5]}};", diag::RangeOOB},
        {"byte b[]; int a = {<<3{b with[3:2]}};", diag::SelectEndianDynamic},
        {"byte b[], c[4]; always {>>{b, {<<3{c with[b[0]:b[1]]}}}} = 9;", diag::BadStreamWithOrder},
        {"int a[],b[],c[];bit d;always {>>{b}}={<<{a with [2+:3],c,d}};", diag::BadStreamSize},
    };

    for (const auto& test : illegal) {
        if (testBitstream(test.sv, test.msg) != 1)
            FAIL_CHECK(test.sv);
    }

    std::string legal[] = {
        R"(
int i_header, i_len,  i_crc, o_header, o_len, o_crc;
byte i_data[], o_data[];
initial begin
    byte pkt[$];
    i_header = 12;
    i_len = 5;
    i_data = new[5];
    i_crc = 42;
    pkt = {<< 8 {i_header, i_len, i_data, i_crc}};
    {<< 8 {o_header, o_len, o_data with [0 +: o_len], o_crc}} = pkt;
end
)"};

    for (const auto& test : legal)
        CHECK(testBitstream(test) == 0);

    std::string foo = R"(
typedef byte ft[];
function ft foo(bit[1:24] bar, int len);
    ft a;
    {<<{a with [0+:len]}} = {>> {bar}};
    return a;
endfunction
localparam ft b = foo(24'h123456,
)";

    CHECK(testBitstream(foo + "2);", diag::BadStreamSize) == 1);
    CHECK(testBitstream(foo + "3);") == 0);
    CHECK(testBitstream(foo + "4);", diag::BadStreamSize) == 1);

    std::string foo1 = R"(
typedef byte ft[];
function ft foo(bit[1:24] bar, int len);
    ft a;
    {<<{a with [0+:len]}} = bar;
    return a;
endfunction
localparam ft b = foo(24'h123456,
)";

    CHECK(testBitstream(foo1 + "2);") == 0);
    CHECK(testBitstream(foo1 + "3);") == 0);
    CHECK(testBitstream(foo1 + "4);", diag::BadStreamSize) == 1);
}

TEST_CASE("Class handle expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    class C; endclass
    C c1 = null;
    C c2 = c1;

    initial begin
        if (c1 == c2 || c1 == null || c1 !== null || c2 === c1) begin
        end

        if (c1) begin
            c2 = c1 ? c1 : null;
        end
    end

    int arr[C];
    initial begin
        arr[c1] = 1;
        arr[c2] = 2;
        arr[null] = 3;
    end

    function automatic int bar;
        C c = null;
        C d, e;

        int i = (c == null) ? 1 : 0;
        if (c)
            i++;

        c = 'x ? d : e;
        c = d ? null : e;
        return i + (c ? 0 : 1);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("chandles") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    chandle c1 = null;
    chandle c2 = c1;

    initial begin
        if (c1 == c2 || c1 == null || c1 !== null || c2 === c1) begin
        end

        if (c1) begin
            c2 = c1 ? c1 : null;
        end
    end

    int arr[chandle];
    initial begin
        arr[c1] = 1;
        arr[c2] = 2;
        arr[null] = 3;
    end

    localparam int foo = bar();
    function automatic int bar;
        chandle c = null;
        chandle d, e;

        int i = (c == null) ? 1 : 0;
        if (c)
            i++;

        c = 'x ? d : e;
        c = d ? null : e;
        return i + (c ? 0 : 1);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("chandle errors") {
    auto tree = SyntaxTree::fromText(R"(
module m(input chandle c1);
    chandle c2;
    always @(c2) begin end
    assign c2 = c1;

    union { chandle c3; } asdf;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidPortType);
    CHECK(diags[1].code == diag::AssignToCHandle);
    CHECK(diags[2].code == diag::InvalidUnionMember);
}

TEST_CASE("Event data type") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    event c1 = null;
    event c2 = c1;

    initial begin
        if (c1 == c2 || c1 == null || c1 !== null || c2 === c1) begin
        end

        if (c1) begin
            c2 = c1 ? c1 : null;
        end

        if (c1.triggered || c2.triggered()) begin end
    end

    int arr[event];
    initial begin
        arr[c1] = 1;
        arr[c2] = 2;
        arr[null] = 3;
    end

    localparam int foo = bar();
    function automatic int bar;
        event c = null;
        event d, e;

        int i = (c == null) ? 1 : 0;
        if (c)
            i++;

        c = 'x ? d : e;
        c = d ? null : e;
        return i + (c ? 0 : 1);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface data type") {
    auto tree = SyntaxTree::fromText(R"(
interface Foo;
    logic i;
    modport m(output i);
endinterface

module m;
    Foo f();
    virtual interface Foo a = null;
    virtual Foo.m b = a;

    initial begin
        if (a == b || a == null || a !== null || b === a) begin
        end

        if (a) begin
            b = a ? a : null;
        end

        a = f;
        b = f;
        b = f.m;
        a.i = 1;
        b.i = 0;
    end

    typedef virtual Foo ft;
    int arr[ft];
    initial begin
        arr[a] = 1;
        arr[null] = 3;
    end

    localparam int foo = bar();
    function automatic int bar;
        ft c = null;
        ft d, e;

        int i = (c == null) ? 1 : 0;
        if (c)
            i++;

        c = 'x ? d : e;
        c = d ? null : e;
        return i + (c ? 0 : 1);
    endfunction

    function void baz(virtual Foo asdf);
    endfunction

    Foo farray[3] ();
    initial baz(farray[1]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("string concat lvalue error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int i = foo();
    function int foo();
        string a, b;
        {a, b} = "asdf asdf";
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
}

TEST_CASE("Implicit param string literal propagation") {
    auto tree = SyntaxTree::fromText(R"(
module n #(parameter foo);
    string s;
    initial s = foo;
endmodule

module m;
    localparam f = "asdf";
    n #(f) n1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Compound assignment checking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a[3];
    int i;
    initial begin
        a += a;
        i %= 3.14;
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

TEST_CASE("Implicit conversion warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { logic a; int b; } foo;
    union packed { int a; int b; } bar;
    logic [43:0] i;
    int j;
    logic [2:0] b;

    initial begin
        foo = bar;
        i = b;
        b = #1 j;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ImplicitConvert);
    CHECK(diags[1].code == diag::WidthExpand);
    CHECK(diags[2].code == diag::SignConversion);
    CHECK(diags[3].code == diag::WidthTruncate);
}

TEST_CASE("Assign to net in procedural context") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire i;
    initial i = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AssignToNet);
}

TEST_CASE("Selects of vectored nets") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire vectored integer i;
    wire j = i[1];
    wire [1:0] k = i[1:0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::SelectOfVectoredNet);
    CHECK(diags[1].code == diag::SelectOfVectoredNet);
}

TEST_CASE("Initializing based on own variable") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum { A, B } e = e.first;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Error for missing parens in invocation") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo;
        return 1;
    endfunction
    int i = foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MissingInvocationParens);
}

TEST_CASE("Invoke task declared later") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial foo;
    task foo; endtask
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Array method with-clause plumbing") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef struct { int i; } asdf_t;
    function asdf_t foo;
    endfunction

    asdf_t a = '{default:0};

    int j = foo().i();
    int k = foo().i with (bar);
    int l = a.i with (bar);
    int m = foo() with (bar);
    int n = $bits(a) with (bar);

    int o[3] = '{default:0};
    int p = o.and(a);
    int q = o.and();
    int r = o.and with (1) { 1; };
    int s = o.and with;
    int t = o.and with (a, b);
    int u = o.and(a, b, c) with (a == 1);
    int v = o.and(a[1]) with (a == 1);
    int w = o.and(,) with (a == 1);
    int x = o.and(a, .foo()) with (a == 1);
    int y = o.and(posedge clk) with (a == 1);

    // These are ok.
    int z = o.and(b) with (b + 1);
    int aa = o.and with (item + x);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 14);
    CHECK(diags[0].code == diag::ExpressionNotCallable);
    CHECK(diags[1].code == diag::UnexpectedWithClause);
    CHECK(diags[2].code == diag::UnexpectedWithClause);
    CHECK(diags[3].code == diag::WithClauseNotAllowed);
    CHECK(diags[4].code == diag::WithClauseNotAllowed);
    CHECK(diags[5].code == diag::IteratorArgsWithoutWithClause);
    CHECK(diags[6].code == diag::UnexpectedConstraintBlock);
    CHECK(diags[7].code == diag::ExpectedIterationExpression);
    CHECK(diags[8].code == diag::ExpectedIterationExpression);
    CHECK(diags[9].code == diag::TooManyArguments);
    CHECK(diags[10].code == diag::ExpectedIteratorName);
    CHECK(diags[11].code == diag::EmptyArgNotAllowed);
    CHECK(diags[12].code == diag::NamedArgNotAllowed);
    CHECK(diags[13].code == diag::InvalidArgumentExpr);
}

TEST_CASE("Iterator index method") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[3] = '{default:0};
    int i = foo.sum(a) with (a + a.index);

    int bar[string] = '{"hello": 0};
    int k = bar.sum(b) with (b.index().atoi);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unbounded queue access") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter int u = $;
    parameter v = $;
    parameter w = $+1;

    int q[$] = { 2, 4, 8 };
    int e, pos;
    initial begin
        e = q[$];
        q[$] = 1;
        q[$+1] = 2;
        q = q[1:$];
        q = q[0:$-1];
        q = { q[0:pos-1], e, q[pos:$] };
        q = { q[0:pos], e, q[pos+1:$] };
        q = q[2:$];
        q = q[1:$-1'b1];
        q = q[1:e != 0 ? $+1 : $-1];

        // These are disallowed.
        e = $;
        q[-$] = 1;
        e = u;
        e = v;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UnboundedNotAllowed);
    CHECK(diags[1].code == diag::UnboundedNotAllowed);
    CHECK(diags[2].code == diag::UnboundedNotAllowed);
    CHECK(diags[3].code == diag::UnboundedNotAllowed);
    CHECK(diags[4].code == diag::UnboundedNotAllowed);
}

TEST_CASE("Selects with negative bounds") {
    auto tree = SyntaxTree::fromText(R"(
module foo;
   wire [-1:0] fred;
   assign      fred = 1;

   initial begin
      if (fred[0] !== 1) begin end
      if (fred[-1] !== 0) begin end
   end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type reference expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    bit [12:0] a, b;
    parameter type b_t = type(a);
    case (type(b_t))
        type(bit[12:0]): begin: b1 initial $display("asdf"); end
        type(real): begin: b2 initial $display("foo"); end
    endcase

    function int foo;
        case (type(b_t))
            type(bit[12:0]) : return 8;
            default         : return -1;
        endcase
    endfunction

    localparam int c = type(b_t) == type(bit[12:0]);
    localparam int d = type(b_t) !== type(bit[12:0]);
    localparam int e = foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    CHECK(!root.lookupName<GenerateBlockSymbol>("m.b1").isUninstantiated);
    CHECK(root.lookupName<GenerateBlockSymbol>("m.b2").isUninstantiated);

    auto& c = root.lookupName<ParameterSymbol>("m.c");
    CHECK(c.getValue().integer() == 1);

    auto& d = root.lookupName<ParameterSymbol>("m.d");
    CHECK(d.getValue().integer() == 0);

    auto& e = root.lookupName<ParameterSymbol>("m.e");
    CHECK(e.getValue().integer() == 8);
}

TEST_CASE("Casting with type references") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    bit [12:0] a, b;
    var type(a+b) c, d;
    initial c = type(a+13'd3)'(d[7:0]);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assignment pattern with type references") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct { int a; int b; int c; } a;
    parameter bar = type(a)'{1, 2, 3};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid property expression in normal subroutine call") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function f(int i); endfunction
    int i = f(3 iff 4);
    int j = f((((4)[*3])));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidArgumentExpr);
    CHECK(diags[1].code == diag::InvalidArgumentExpr);
}

TEST_CASE("Subroutine invocation") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function f(int i); endfunction
    int i = f((3));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid specparam regress GH #417") {
    auto tree = SyntaxTree::fromText(R"(
specparam[] asasa = 1;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no assertion.
    compilation.getAllDiagnostics();
}

TEST_CASE("Invalid argument regress GH #418") {
    auto tree = SyntaxTree::fromText(R"(
byte i_data [ ] ;
initial
i_data [ 12 : 9
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no assertion.
    compilation.getAllDiagnostics();
}

TEST_CASE("Tagged union expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    union tagged { int a; int b[]; void c; } foo;
    initial begin
        foo = tagged a 1;
        foo = tagged b '{1,2};
        foo = tagged c;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Tagged union expression errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    union tagged { int a; int b[]; void c; } foo;
    initial begin
        i = 1 + tagged a;
        foo = tagged baz 1;
        foo = tagged b;
        foo = tagged c 52;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::TaggedUnionTarget);
    CHECK(diags[1].code == diag::UnknownMember);
    CHECK(diags[2].code == diag::TaggedUnionMissingInit);
    CHECK(diags[3].code == diag::BadAssignment);
}

TEST_CASE("Assignment pattern expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    // Simple patterns, different target types
    struct packed { int a; logic [3:0] b; } a = '{9000, 13};
    struct { int a; real b; } b = '{1, 3.14};
    logic [3:1][2:5] c = '{3'd2, 3'd5, 3'd6};
    real d[2:5] = '{1.1, 1.2, 1.3, 1.4};
    int e[] = '{0:1, 1:2, 2:3};
    int f[*] = '{1:1, 2:2, 3:3};
    int g[$] = '{3 {1}};
    enum logic[1:0] { A, B } h = '{1, 0};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assignment pattern errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    event e1 = event'{1};
    parameter p = '{1, 2};

    typedef event e_t;
    e_t e2 = '{1};

    int a[int] = '{1, 2};

    typedef real rt;
    typedef struct { int a; rt b; } st;
    st b = '{1};
    int c[1:2] = '{1};
    st d = '{default:1, default:2, a:1, a:2, rt:3.14, blah:3, event:1, (1+1):2};

    int e[] = '{0:1, 0:2, default:1, int:3, -1:2};
    int f[1:2] = '{default:1, default:2, event:1, 9:1};
    int g[] = '{1:1};

    st h = '{-1{0}};
    st i = '{3{1}};
    int j[1:2] = '{-1{0}};
    int k[] = '{-1{0}};

    int l[int] = '{default:1, default:2, 3:1, 3:2, int:1};

    int m[2][2] = '{real:3.14};
    struct { int i; real r; } n[2] = '{real:3.14};

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 28);
    CHECK(diags[0].code == diag::BadAssignmentPatternType);
    CHECK(diags[1].code == diag::AssignmentPatternNoContext);
    CHECK(diags[2].code == diag::BadAssignmentPatternType);
    CHECK(diags[3].code == diag::AssignmentPatternAssociativeType);
    CHECK(diags[4].code == diag::WrongNumberAssignmentPatterns);
    CHECK(diags[5].code == diag::WrongNumberAssignmentPatterns);
    CHECK(diags[6].code == diag::AssignmentPatternKeyDupDefault);
    CHECK(diags[7].code == diag::AssignmentPatternKeyDupName);
    CHECK(diags[8].code == diag::UnknownMember);
    CHECK(diags[9].code == diag::AssignmentPatternKeyExpr);
    CHECK(diags[10].code == diag::AssignmentPatternKeyExpr);
    CHECK(diags[11].code == diag::AssignmentPatternKeyDupValue);
    CHECK(diags[12].code == diag::AssignmentPatternDynamicDefault);
    CHECK(diags[13].code == diag::AssignmentPatternDynamicType);
    CHECK(diags[14].code == diag::ValueMustBePositive);
    CHECK(diags[15].code == diag::AssignmentPatternKeyDupDefault);
    CHECK(diags[16].code == diag::AssignmentPatternKeyExpr);
    CHECK(diags[17].code == diag::IndexValueInvalid);
    CHECK(diags[18].code == diag::AssignmentPatternMissingElements);
    CHECK(diags[19].code == diag::ValueMustBePositive);
    CHECK(diags[20].code == diag::WrongNumberAssignmentPatterns);
    CHECK(diags[21].code == diag::ValueMustBePositive);
    CHECK(diags[22].code == diag::ValueMustBePositive);
    CHECK(diags[23].code == diag::AssignmentPatternKeyDupDefault);
    CHECK(diags[24].code == diag::AssignmentPatternKeyDupValue);
    CHECK(diags[25].code == diag::AssignmentPatternDynamicType);
    CHECK(diags[26].code == diag::AssignmentPatternMissingElements);
    CHECK(diags[27].code == diag::AssignmentPatternNoMember);
}

TEST_CASE("Set membership type checking regress GH #450") {
    auto tree = SyntaxTree::fromText(R"(
string val;
function compare(string attr[$]);
    if (val inside {attr}) begin
    end
endfunction
function compare_singular(string attr1, string attr2);
    if (val inside {attr1, attr2}) begin
    end
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assignment assertion regress GH #456") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum { A, B } foo;
    int bar;
    initial begin
        case (bar)
            A: begin end
            default;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CaseTypeMismatch);
}

TEST_CASE("Binary expression regress GH #457") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire a;
    always @((a) && (a)) begin end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Expression lookup regress GH #470") {
    auto tree = SyntaxTree::fromText(R"(
typedef logic [$ clog2:0] clearing_lfsr_perm_t;
function aes_sb_out_mask_prd_concat;
sb_out_mask_prd [ $ clog2 () ' ( RomSize ) ] ;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}

TEST_CASE("Nested call expressions") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    function int foo(int i); endfunction
    function A func; endfunction
endclass

module m;
    A bar = new;
    int i = bar.func().foo(3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("evalLValue crash if lhs not implemented") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a;
    initial begin
        if ((m.a = 1) == 2) begin
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bad conversion diagnostic in lvalue") {
    auto tree = SyntaxTree::fromText(R"(
typedef enum { A, B } foo;
module m(output int i);
endmodule

module top;
    foo i;
    m m1(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("Multiple driver errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { int foo; } [1:0] bar[3];

    assign bar[0][0].foo = 1;
    assign bar[0][0].foo = 2;
    assign bar[1] = '0;

    initial begin
        bar[1][0] = '1;
        bar[2][0].foo = 1;
        bar[2][0].foo = 2;
    end

    assign bar[2][1].foo = 3;

    int i = 1;
    assign i = 2;

    wire [31:0] j = 1;
    assign j = 2;

    uwire [31:0] k = 1;
    assign k = 2;

    nettype real nt;
    nt n = 3.14;
    assign n = 2.3;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MixedVarAssigns);
    CHECK(diags[2].code == diag::MixedVarAssigns);
    CHECK(diags[3].code == diag::MultipleUWireDrivers);
    CHECK(diags[4].code == diag::MultipleUDNTDrivers);
}

TEST_CASE("Recursive function in always_comb driver check") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  logic passed;
  logic [7:0] value;
  integer ones;

  function automatic integer count_by_one(input integer start);
    if (start != 0) count_by_one = (value[start] ? 1 : 0) + count_ones(start-1);
    else count_by_one = value[start] ? 1 : 0;
  endfunction

  function automatic integer count_ones(input integer start);
    if (start != 0) count_ones = (value[start] ? 1 : 0) + count_by_one(start-1);
    else count_ones = value[start] ? 1 : 0;
  endfunction

  always_comb ones = count_ones(7);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("String literal binary op const eval regress") {
    auto tree = SyntaxTree::fromText(R"(
parameter string foo = "hello";
parameter string bar = {foo, "0" | 5};
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& bar = compilation.getRoot().compilationUnits[0]->lookupName<ParameterSymbol>("bar");
    CHECK(bar.getValue().str() == "hello5");
}

TEST_CASE("Clocking block synchronous drive regress GH #543") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    logic clk;
    logic [31:0] a;

    default clocking cb @(posedge clk);
        output a;
    endclocking

endinterface

class C;
    virtual I intf;
    rand bit b;

    virtual task t();
        fork begin
            for (int i = 0; i < 4; i++) begin
                intf.cb.a[10] <= b;
                if (b) begin
                    #100;
                    intf.cb.a[10] <= '0;
                end
                #100;
            end
        end join_none
    endtask
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bits of non-static var allowed in static init") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  initial begin
    automatic int a = 1;
    static logic [$bits(a)-1:0] b;
  end
endmodule

class C;
    int a;
    static int b = $bits(a);
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("String out-of-bounds accesses") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam string s = "asdf";
    int i = s[2:3];

    localparam byte j = foo();
    function byte foo;
        automatic string t = s;
        t[11] += 4;
        return t[12];
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::BadSliceType);
    CHECK(diags[1].code == diag::ConstEvalDynamicArrayIndex);
    CHECK(diags[2].code == diag::ConstEvalDynamicArrayIndex);
}

TEST_CASE("Out-of-bounds element selects in consteval") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam string s[integer] = '{0: "hello", 2: "world"};
    localparam string t = s[1];
    localparam logic[6:1] u = 4;

    localparam int i = foo();

    int bar;
    function automatic int foo;
        string k = s['x];
        logic l1 = 'x;
        byte b = t[l1];
        int q = 9;
        logic l2 = u[q];

        k[bar] = 1;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::ConstEvalAssociativeElementNotFound);
    CHECK(diags[1].code == diag::ConstEvalAssociativeIndexInvalid);
    CHECK(diags[2].code == diag::IndexOOB);
    CHECK(diags[3].code == diag::IndexOOB);
    CHECK(diags[4].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
}

TEST_CASE("Out-of-bounds range selects in consteval") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string s[integer] = '{0: "hello", 2: "world"};
    string t = s[2:1];

    real r = 1.0;
    logic [7:0] u = 0;
    logic [1:0] v1 = u[r:0];
    logic [1:0] v2 = u[0:r];
    logic [1:0] v3 = u[1:2];
    logic [1:0] v4 = u[1+:-1];
    logic [9:0] v5 = u[1+:10];
    logic [1:0] v6 = u['x+:2];
    logic [9:0] v7 = u[u+:10];

    int w[] = {1};
    int x1[2] = w[u:1];
    int x2[2] = w[u+:-1];

    localparam int y[5] = {1,2,3,4,5};

    localparam int i1 = f1();
    localparam int i2 = f2();
    localparam int i3 = f3();
    localparam int i4 = f4();
    localparam int i5 = f5();
    localparam int i6 = f6();

    function automatic int f1;
        int a = -1;
        int b[] = y[a+:3];
        w[0:1] = {1,1};
    endfunction

    function automatic int f2;
        int c[];
        c[u+:2] = {1,2};
    endfunction

    function automatic int f3;
        integer a = 'x;
        int c[];
        c[a+:2] = {1,2};
    endfunction

    function automatic int f4;
        integer a = 'x;
        int c[$];
        c[2+:a] = {1,2};
    endfunction

    function automatic int f5;
        integer a = 'x;
        int c[3];
        int d[2] = c[a+:2];
    endfunction

    function automatic int f6;
        int c[];
        int d[20] = c[-10+:20];
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 17);
    CHECK(diags[0].code == diag::RangeSelectAssociative);
    CHECK(diags[1].code == diag::ExprMustBeIntegral);
    CHECK(diags[2].code == diag::ExprMustBeIntegral);
    CHECK(diags[3].code == diag::SelectEndianMismatch);
    CHECK(diags[4].code == diag::ValueMustBePositive);
    CHECK(diags[5].code == diag::RangeOOB);
    CHECK(diags[6].code == diag::IndexValueInvalid);
    CHECK(diags[7].code == diag::RangeWidthOOB);
    CHECK(diags[8].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[9].code == diag::ValueMustBePositive);
    CHECK(diags[10].code == diag::RangeOOB);
    CHECK(diags[11].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
    CHECK(diags[12].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
    CHECK(diags[13].code == diag::IndexValueInvalid);
    CHECK(diags[14].code == diag::IndexValueInvalid);
    CHECK(diags[15].code == diag::IndexValueInvalid);
    CHECK(diags[16].code == diag::ConstEvalDynamicArrayRange);
}

TEST_CASE("Index oob tryEval regress GH #602") {
    auto tree = SyntaxTree::fromText(R"(
module top #(
    parameter [2:0][4:0] IDX_MAP = '{5'd1, 5'd3, 5'd4}
);
    logic [4:0] sig;

    always_comb begin
        for (int n = 0; n < 3; n++) begin
            if (sig[IDX_MAP[n]] != 'h0) begin
            end
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Index invalid expression regress GH #675") {
    auto tree = SyntaxTree::fromText(R"(
virtual class C #(type enum_t = int);
    static function enum_t str2enum(string str);
        static enum_t enum_type_map[string];
        enum_t e;

        if (enum_type_map.exists(str)) begin
            e = enum_type_map[str];
        end else begin
            e = e.first();
        end

        return e;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Proc subroutine multiple driver tracking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [9:0] a;
    always_comb begin
        for (int i = 0; i < $size(a); i++)
            a[i] = 0;
        baz();
        baz();
    end

    task baz;
        a[0] = 1;
    endtask
endmodule
)");

    // This tests a crash due to invalidating iterators while
    // iterating the variable's driver map.
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("String constant expression error regress GH #811") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    string s3[string];
    function void f();
        if (s3.exists("abcdef")) begin
        end
    endfunction
endclass

class C;
    A a;
    function void f();
        string s1 = "abcdef";
        string s2 = "abc";
        a = new();

        if (s1.substr(0, 2) == s2) begin
        end
        if (s1 == s2) begin
        end
        if (a.s3.exists("abcdef")) begin
        end
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Type of unsized based literal") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    parameter p = 'd999999999999;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& p = compilation.getRoot().lookupName<ParameterSymbol>("m.p");
    CHECK(p.getType().toString() == "logic[39:0]");
}

TEST_CASE("Stream operator size overflow") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i[];
    int j[99999999];
    assign i = {<< {j, j, j with [0+:400000000]}};

    int k[$];
    int l[];
    always_comb l = {<< {k with [0+:999999999]}};

    typedef struct { int i[400000000]; logic l[$]; } asdf;
    asdf n [999999][][999999][];
    int o[];
    always {<< {o}} = {<< {n}};

    struct { asdf a[]; int i[400000000]; logic l; } p;
    always {<< {p}} = {<< {o}};

    class C;
        asdf n [999999][][999999][];
    endclass
    C c;
    always {<< {o}} = {<< {c}};

    class D;
        int a[];
        int b[400000000];
    endclass
    D d;
    always {<< {o}} = {<< {d, d, d}};
endmodule

function automatic int func1;
    typedef struct { int a[]; int i[400000000]; logic l; } asdf;
    struct { asdf a[]; bit b; asdf c; } p[];
    int o[] = {1};
    {<< {p}} = {<< {o}};
    return 0;
endfunction

function automatic int func2;
    typedef struct { int a[]; int i[400000000]; logic l; } asdf;
    struct { asdf a[]; bit b; asdf c; } p[];
    int o[] = {1};
    {<< {p}} = o;
    return 0;
endfunction

function automatic int func3(int a, int b);
    int foo[3];
    {<< {foo with [a:b]}} = 5;
endfunction

module n;
    localparam int q = func1();
    localparam int r = func2();
    localparam int s = func3(1, 1000000000);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::ObjectTooLarge);
    CHECK(diags[1].code == diag::RangeOOB);
    CHECK(diags[2].code == diag::ObjectTooLarge);
    CHECK(diags[3].code == diag::BadStreamSize);
    CHECK(diags[4].code == diag::BadStreamSize);
    CHECK(diags[5].code == diag::BadStreamSize);
    CHECK(diags[6].code == diag::BadStreamSize);
    CHECK(diags[7].code == diag::BadStreamSize);
    CHECK(diags[8].code == diag::BadStreamSize);
    CHECK(diags[9].code == diag::RangeOOB);
    CHECK(diags[10].code == diag::ObjectTooLarge);
}

TEST_CASE("Index OOB unevaluated context when checking implicit conversions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam logic foo[10] = '{default:0};
    for (genvar i = 0; i < 10; i++) begin
        localparam int k = i == 0 ? 9 : foo[i - 1];
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assignment patterns as lvalues") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef byte U[3];
    function automatic U f1;
        var U A = '{1, 2, 3};
        var byte a, b, c;
        '{a, b, c} = A;
        U'{c, a, b} = '{a+1, b+1, c+1};
        return {a, b, c};
    endfunction

    typedef struct packed { int i; logic j; } V;
    function automatic V f2;
        V v = '{32, 1};
        int i;
        logic j;
        '{i, j} = v;
        return '{i, j};
    endfunction

    typedef struct { real r; string s; } W;
    function automatic W f3;
        W w = '{3.14, "Hello World"};
        real r;
        string s;
        '{r, s} = w;
        return '{r, s};
    endfunction

    localparam U u = f1();
    localparam V v = f2();
    localparam W w = f3();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto& u = root.lookupName<ParameterSymbol>("m.u");
    CHECK(u.getValue().toString() == "[8'sd3,8'sd4,8'sd2]");

    auto& v = root.lookupName<ParameterSymbol>("m.v");
    CHECK(v.getValue().integer() == 65);

    auto& w = root.lookupName<ParameterSymbol>("m.w");
    CHECK(w.getValue().toString() == "[3.14,\"Hello World\"]");
}

TEST_CASE("Invalid assigment pattern lvalues") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef struct { real r; string s; } U;
    function automatic void f1;
        real r;
        string s;
        U'{r:r, s:s} = '{3.14, "Hello World"};
    endfunction

    function automatic void f2;
        int i[];
        int j, k;
        '{j, k} = i;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
    CHECK(diags[1].code == diag::AssignmentPatternLValueDynamic);
}

TEST_CASE("Invalid select after range select") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo; return 1; endfunction

    int i;
    int j = i[3:0][0];
    int k = foo()[3:0][0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::SelectAfterRangeSelect);
    CHECK(diags[1].code == diag::SelectAfterRangeSelect);
}

TEST_CASE("Streaming concat in non-stream context") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [16777214:0] a;
    int i = {<<{a, a}} + 1;

    let known(sig) = (!($isunknown({>>{sig}})));

    property known_prop(sig, clk);
      @(clk) (!($isunknown({>>{sig}})));
    endproperty

    wire clk;
    assert property (known_prop(known(clk), clk));
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowSelfDeterminedStreamConcat;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadStreamSize);
}

TEST_CASE("Multi-driven errors through call expressions from normal always block") {
    auto tree = SyntaxTree::fromText(R"(
module top(input clk, input reset);
    logic c;
    function logic m(logic d);
        c = d;
        return c;
    endfunction

    logic a, b;
    always_ff @(posedge clk) begin
        a <= m(a);
    end

    always @(posedge reset) begin
        b <= m(a);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Multi-driven subroutine local var option to allow") {
    auto tree = SyntaxTree::fromText(R"(
module top(input clk, input reset);
    function logic m(logic d);
        logic c;
        c = d;
        return c;
    endfunction

    logic a, b;
    always_ff @(posedge clk) begin
        a <= m(a);
    end

    always @(posedge reset) begin
        b <= m(a);
    end
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowMultiDrivenLocals;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023 clarification: multi-driven subroutine checking doesn't apply to tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    task t;
        i <= 1;
    endtask

    always_comb t();
    always_comb t();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: Unsized integer literals can be any bit width") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam a = 'h7_0000_0000;
    localparam b = 4294967296;
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto getParam = [&](std::string_view name) -> decltype(auto) {
        return compilation.getRoot().lookupName<ParameterSymbol>(name);
    };

    auto& a = getParam("m.a");
    auto& b = getParam("m.b");
    CHECK(a.getType().toString() == "logic[34:0]");
    CHECK(b.getType().toString() == "logic signed[33:0]");
    CHECK(a.getValue().integer() == 0x700000000ull);
    CHECK(b.getValue().integer() == 4294967296ll);
}

TEST_CASE("Change of behavior in time literal rounding") {
    // 1800-2023 changed the rules for time literals; previously they would
    // be scaled and rounded to the current time settings, but now they are
    // only scaled, not rounded. This is a breaking change, but it turns out
    // they made this change because no other tools ever implemented the
    // rounding part of the rule, so slang just needs to conform.
    auto tree = SyntaxTree::fromText(R"x(
module test();
  timeunit 1ns/1ps;

    if (1.0 == 1ns)
      $info("TEST1 PASSED");
    else
      $info("TEST1 FAILED");

    if (1fs == 10fs)
      $info("TEST2 PASSED");
    else
      $info("TEST2 FAILED");

    if (1fs == 0.000001)
      $info("TEST3 FAILED (SCALED/!ROUNDED)");
    else
      if (1fs == 0.000000000000001)
        $info("TEST3 FAILED (!SCALED/!ROUNDED)");
      else
        if (1fs == 0.0)
          $info("TEST3 PASSED");
        else
          $info("TEST3 REALLY FAILED");
endmodule : test
)x");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // This used to print TEST PASSED for all three tests,
    // but now it prints what all other tools print.
    auto& diags = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diags);
    CHECK(result == R"x(
source:6:7: note: $info encountered: TEST1 PASSED
      $info("TEST1 PASSED");
      ^
source:13:7: note: $info encountered: TEST2 FAILED
      $info("TEST2 FAILED");
      ^
source:16:7: note: $info encountered: TEST3 FAILED (SCALED/!ROUNDED)
      $info("TEST3 FAILED (SCALED/!ROUNDED)");
      ^
)x");
}

TEST_CASE("Set membership can use unbounded literals") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam a = $;
    localparam b = 10;
    localparam c = 15 inside {[b:a]};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& c = compilation.getRoot().lookupName<ParameterSymbol>("m.c");
    CHECK(c.getValue().integer() == 1);
}

TEST_CASE("Chained method calls require parentheses") {
    auto tree = SyntaxTree::fromText(R"(
string sa[10] = '{default:"SDF"};
int i = sa.unique.size;
int j = sa.unique().size;

int ia[10] = '{default:0};
int k[$] = ia.find(x) with (x > 5).unique;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ChainedMethodParens);
}

TEST_CASE("v1800-2023: override name of index method") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
function automatic f;
    typedef struct {int index;} idx_type;
    idx_type arr1[4];
    idx_type arr2[$] = arr1.find(item, iter_index) with (item.index != item.iter_index);
endfunction
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Overriding index method name not allowed in 1800-2017") {
    auto tree = SyntaxTree::fromText(R"(
function automatic f;
    typedef struct {int index;} idx_type;
    idx_type arr1[4];
    idx_type arr2[$] = arr1.find(item, iter_index) with (item.index != item.iter_index);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WrongLanguageVersion);
}

TEST_CASE("v1800-2023 clarification: non-blocking assignments to elements of dynamic arrays are "
          "not allowed") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i[];
    initial begin
        i[0] <= 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NonblockingDynamicAssign);
}

TEST_CASE("v1800-2023 clarification: static casts are assignment-like contexts") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  typedef int DA[];
  localparam p = DA'('{1, 2, 3});
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: value range expressions with tolerance operators") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam a = 5.3 inside { "ASDF", 5.0, [4.0+/-2] };
    localparam b = 5.3 inside { "ASDF", 5.0, [7.0+%-25] };
    localparam c = 5 inside { [7+%-25] };
    localparam d = -6 inside { [-7+%-25] };
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto getValue = [&](std::string_view name) {
        return compilation.getRoot().lookupName<ParameterSymbol>(name).getValue();
    };

    CHECK(getValue("m.a").integer() == 1);
    CHECK(getValue("m.b").integer() == 1);
    CHECK(getValue("m.c").integer() == 0);
    CHECK(getValue("m.d").integer() == 1);
}

TEST_CASE("Multi-driven unpacked array regress GH #923") {
    auto tree = SyntaxTree::fromText(R"(
// Range select in unpacked array, causing error.
module Test1;
  parameter DIM1 = 2;
  parameter DIM2 = 4;

  logic test [DIM1-1:0][DIM2-1:0];

  // i == 2, elemRange = {1, 1}, start 1, width 1, elemWidth 4, result = {4, 7}
  // i == 1, elemRange = {1, 3}, start 1, width 3, elemWidth 3, result = {7, 9}, should be {5, 7}
  assign test[0][DIM2-2:0] = '{default: '0};

  // i == 2, elemRange = {1, 1}, start 1, width 1, elemWidth 4, result = {4, 7}
  // i == 1, elemRange = {0, 0}, start 0, width 1, elemWidth 1, result = {4, 4}
  assign test[0][DIM2-1]   = '0;

  // i == 2, elemRange = {0, 0}, start 0, width 1, elemWidth 4, result = {0, 3}
  // i == 1, elemRange = {1, 3}, start 1, width 3, elemWidth 3, result = {3, 5}, should be {1, 3}
  assign test[1][DIM2-2:0] = '{default: '0};

  // i == 2, elemRange = {0, 0}, start 0, width 1, elemWidth 4, result = {0, 3}
  // i == 1, elemRange = {0, 0}, start 0, width 1, elemWidth 1, result = {0, 0}
  assign test[1][DIM2-1]   = '0;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: ref static arguments") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
function automatic foo(ref static a, r);
    static logic l = r;
endfunction

module m;
    logic a, r;
    logic b = foo(a, r);
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: ref static errors") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
function automatic void bar(ref static a);
endfunction

function automatic void foo(ref static a, r);
    bar(a);
endfunction

class C;
    static logic a;
    logic b;
endclass

module m;
    logic r[];
    C c;
    initial begin
        automatic logic a;
        foo(a, r[0]);
        foo(c.a, c.b);
    end
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::AutoVarToRefStatic);
    CHECK(diags[1].code == diag::AutoVarToRefStatic);
    CHECK(diags[2].code == diag::AutoVarToRefStatic);
}

TEST_CASE("Out of range select regress") {
    auto tree = SyntaxTree::fromText(R"(
localparam p = -4'd8;
$info(p[-2147483648:-2147483649]);
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::RangeWidthOverflow);
    CHECK(diags[1].code == diag::SignedIntegerOverflow);
    CHECK(diags[2].code == diag::SignedIntegerOverflow);
}

TEST_CASE("Assigning void in expressions is illegal") {
    auto tree = SyntaxTree::fromText(R"(
function void foo;
endfunction

module m;
     union tagged {
        void a;
        type(a) b;
    } u;

    var type(foo) a;
    var type(u.a) b;

    initial begin
        a = foo();
        u.a = foo();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::TypeRefVoid);
    CHECK(diags[1].code == diag::TypeRefVoid);
    CHECK(diags[2].code == diag::TypeRefVoid);
    CHECK(diags[3].code == diag::VoidAssignment);
    CHECK(diags[4].code == diag::VoidAssignment);
}

TEST_CASE("Virtual interface array concat") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

module m;
    virtual I i[3];
    I i1();
    I i2 [2] ();
    assign i = {i1, i2};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface array concat errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

interface J;
endinterface

module m;
    virtual I i[3];
    I i1();
    J i2 [2] ();
    assign i = {i1, i2};
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadConcatExpression);
}

TEST_CASE("Wrong typename in error regress GH #1013") {
    auto tree = SyntaxTree::fromText(R"(
module t40;
typedef struct {
        logic a;
        logic b;
} t;
t x, y, z;
assign z = x & y;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:8:14: error: invalid operands to binary expression ('t40.t' and 't40.t')
assign z = x & y;
           ~ ^ ~
)");
}

TEST_CASE("IEEE 1800 Section 10.9.2 - structure assignment patterns") {
    auto tree = SyntaxTree::fromText(R"(
module top;
   typedef struct {
      logic [7:0] a;
      bit b;
      bit signed [31:0] c;
      string s;
   } sa;

   sa s2;
   initial s2 = '{int:1, default:0, string:""}; // set all to 0 except the
                                                // array of bits to 1 and
                                                // string to ""
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("LHS assignment pattern bit width checking") {
    auto tree = SyntaxTree::fromText(R"(
function automatic [7:0] f();
    logic [3:0] a, b;
    '{ a, b } = 2'h3;
    return {a, b};
endfunction

typedef logic[1:0] tt[2];
function automatic tt g();
    logic [1:0] a, b;
    int c[2] = '{ 11, 13 };
    '{ a, b } = c;
    return {a, b};
endfunction

function automatic [3:0] h();
    logic [0:0] data[1] = '{1};
    logic [3:0] a;
    '{ a } = data;
    return a;
endfunction

module m;
    localparam p = f();
    localparam q = g();
    localparam r = h();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::WidthExpand);
    CHECK(diags[1].code == diag::WidthExpand);
    CHECK(diags[2].code == diag::SignConversion);
    CHECK(diags[3].code == diag::WidthTruncate);
    CHECK(diags[4].code == diag::ConstantConversion);
    CHECK(diags[5].code == diag::SignConversion);
    CHECK(diags[6].code == diag::WidthTruncate);
    CHECK(diags[7].code == diag::ConstantConversion);
    CHECK(diags[8].code == diag::WidthExpand);

    auto& p = compilation.getRoot().lookupName<ParameterSymbol>("m.p");
    CHECK(p.getValue().integer() == "8'b00010001"_si);

    auto& q = compilation.getRoot().lookupName<ParameterSymbol>("m.q");
    CHECK(q.getValue().toString() == "[2'b11,2'b1]");

    auto& r = compilation.getRoot().lookupName<ParameterSymbol>("m.r");
    CHECK(r.getValue().toString() == "4'b1");
}

TEST_CASE("Invalid selection driver bounds regress -- GH #1141") {
    auto tree = SyntaxTree::fromText(R"(
module test;
  reg [15:0] vect;

  initial begin
    vect[1 -: 4] = 8'b1010_1010;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::RangeOOB);
    CHECK(diags[1].code == diag::ConstantConversion);
}

TEST_CASE("Empty queue assignment to unknown type placeholder -- GH #1146") {
    auto tree = SyntaxTree::fromText(R"(
class cls#(type T = int);
  int q1[$] = {};
  T q2[$] = {};
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Pattern var in static initializer") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct {int a; real b;} s;
    initial begin
        static int b = s matches '{a:.i, b:.j} ? i : 0;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Boolean convertible types can be used with operator! -- GH #1208") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    chandle handle = null;
    always_comb begin
        if (!handle) begin
            $fatal(1, "handle is null");
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Static casts propagate type correctly and don't truncate") {
    auto tree = SyntaxTree::fromText(R"(
typedef logic [6:0] lt;
function automatic logic[7:0] foo;
    logic [7:0] a = 8'hff;
    lt b = lt'(a >> 1);
    return 8'(b);
endfunction

$static_assert(foo() == 8'h7f);
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Test ternary operation sizing regression") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  logic [3:0] w = (0) ? '0 : '0;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto& var = root.lookupName<VariableSymbol>("m.w");

    ast::EvalContext eval_ctx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max));
    CHECK(var.getInitializer()->eval(eval_ctx).getBitstreamWidth() == 4);
}

TEST_CASE("Value range where implicit strings not allowed") {
    auto tree = SyntaxTree::fromText(R"(
int i = "a" inside { [1:2] };
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("LValue required for prefix unary operators") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        ++(1 + 1);
        (1 + 1)++;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
    CHECK(diags[1].code == diag::ExpressionNotAssignable);
}

TEST_CASE("More operator eval tests") {
    auto tree = SyntaxTree::fromText(R"(
parameter p = foo();

function automatic bit foo;
    shortreal a = 1.0;
    int b = 3;
    string s;
    event ev;
    union { int i; shortreal r; } u, v;

    assert(++a == shortreal'(2.0));
    assert(a++ == shortreal'(2.0));
    --a;
    assert(a-- == shortreal'(2.0));
    assert(+b == 3);
    assert(^4'b1000 == 1);
    assert(~&4'b1111 == 0);
    assert(~|4'b0000 == 1);
    assert(~^4'b1000 == 0);
    assert(+a == shortreal'(1.0));
    assert(-a == shortreal'(-1.0));
    assert((!a) == 0);
    assert((!s) == 1);
    assert(a === shortreal'(1.0));
    assert(!(a !== shortreal'(1.0)));
    assert(a && 1);
    assert(a || 0);
    assert(0 || b);
    assert(0 || 1.0);
    assert(1 -> a);
    assert(1.0 <-> a);
    assert(a <-> 1.0);
    assert(1.0 && 1.0);
    assert(0.0 || 1.0);
    assert(3 % 2 == 1);
    assert(3 !== 2);
    assert(3'b1x0 !=? 3'b111);
    assert(1 <-> 1);
    assert(s === "");
    assert(s !== "asdf");
    assert(ev === null);
    assert(!(ev != null));
    assert(!(ev !== null));

    assert(u === v);
    u.i = 1;
    v.r = 1.0;
    assert(u != v);
    assert(u !== v);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto diags = compilation.getAllDiagnostics().filter({diag::FloatBoolConv, diag::IntBoolConv});
    if (!diags.empty()) {
        FAIL_CHECK(report(diags));
    }
}

TEST_CASE("Referring to instance array in expression -- GH #1314") {
    auto tree = SyntaxTree::fromText(R"(
module subm();
endmodule
module top();
	subm inst[3:0]();
	wire w = inst[0];

    for (genvar i = 0; i < 2; i++) begin : asdf
    end
    int i = asdf[0];
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NotAValue);
    CHECK(diags[1].code == diag::NotAValue);
}
