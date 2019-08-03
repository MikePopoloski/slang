#include "Test.h"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

SVInt testParameter(const std::string& text, uint32_t index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(string_view(fullText));

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& module = *compilation.getRoot().topInstances[0];
    if (!tree->diagnostics().empty())
        WARN(report(tree->diagnostics()));

    const ParameterSymbol& param = module.memberAt<ParameterSymbol>(index);
    return param.getValue().integer();
}

TEST_CASE("Bind parameter") {
    CHECK(testParameter("parameter foo = 4;") == 4);
    CHECK(testParameter("parameter foo = 4 + 5;") == 9);
    CHECK(testParameter("parameter bar = 9, foo = bar + 1;", 1) == 10);
    CHECK(testParameter("parameter logic [3:0] foo = 4;") == 4);
    CHECK(testParameter("parameter logic [3:0] foo = 4'b100;") == 4);
}

TEST_CASE("Evaluate assignment expression") {
    // Evaluate an assignment expression (has an LValue we can observe)
    auto syntax = SyntaxTree::fromText("i = i + 3");

    // Fabricate a symbol for the `i` variable
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto varToken = syntax->root().getFirstToken();
    VariableSymbol local{ varToken.valueText(), varToken.location() };
    local.setType(compilation.getIntType());

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                         BindContext(scope, LookupLocation::max));
    REQUIRE(syntax->diagnostics().empty());

    // Initialize `i` to 1.
    EvalContext context(scope);
    auto i = context.createLocal(&local, SVInt(32, 1, true));

    // Evaluate the expression tree.
    bound.eval(context);
    CHECK(i->integer() == 4);

    // Run it again, results should be as you'd expect
    bound.eval(context);
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
    VariableSymbol local{ varToken.valueText(), varToken.location() };
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                         BindContext(scope, LookupLocation::max));
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
    VariableSymbol local{ varToken.valueText(), varToken.location() };
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                         BindContext(scope, LookupLocation::max));
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
    VariableSymbol local{ varToken.valueText(), varToken.location() };
    local.setType(compilation.getType(20, IntegralFlags::Unsigned));

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = Expression::bind(syntax->root().as<ExpressionSyntax>(),
                                         BindContext(scope, LookupLocation::max));
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
        auto tree = SyntaxTree::fromText(string_view(source));
        scope.getCompilation().addSyntaxTree(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type->toString();
    };

    declare("logic [7:0] l;");
    declare("logic signed [7:0] sl;");
    declare("logic [7:0][3:2] pa;");
    declare("bit [2:10] b1;");
    declare("int i;");
    declare("real r;");
    declare("shortreal sr;");
    declare("struct packed { logic a; bit b; } sp;");
    declare("struct { logic a; bit b; } su;");
    declare("struct { bit a; bit b; } su2;");
    declare("reg reg1, reg2;");

    // Literals / misc
    CHECK(typeof("\"asdfg\"") == "bit[39:0]");
    CHECK(typeof("reg1 + reg2") == "reg");

    // Unary operators
    CHECK(typeof("+i") == "int");
    CHECK(typeof("-sp") == "struct packed{logic a;bit b;}");
    CHECK(typeof("!r") == "bit");
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

    // Unpacked arrays
    declare("bit [7:0] arr1 [2];");
    declare("bit [7:0] arr2 [2:0];");
    declare("bit [7:0] arr3 [3];");
    CHECK(typeof("arr1 == arr2") == "<error>");
    CHECK(typeof("arr2 == arr3") == "bit");
    CHECK(typeof("arr1 == arr3[0:1]") == "bit");

    // Conditional operator
    CHECK(typeof("i ? l : pa") == "logic[15:0]");
    CHECK(typeof("r ? b1 : i") == "bit[31:0]");
    CHECK(typeof("i ? arr2 : arr3") == "bit[7:0]$[2:0]");
    CHECK(typeof("i ? arr1: arr2") == "<error>");
    CHECK(typeof("arr2 ? 1 : 0") == "<error>");

    // Member access
    declare("struct packed { logic [13:0] a; bit b; } foo;");
    declare("struct packed { logic [13:0] a; bit b; } [3:0] spPackedArray;");
    CHECK(typeof("foo.a") == "logic[13:0]");
    CHECK(typeof("spPackedArray") == "struct packed{logic[13:0] a;bit b;}[3:0]");
    CHECK(typeof("spPackedArray[0].a") == "logic[13:0]");

    // Casts
    declare("parameter int FOO = 1;");
    CHECK(typeof("(FOO + 2)'(b1)") == "bit[2:0]");
    CHECK(typeof("int'(b1)") == "int");
    CHECK(typeof("5'(sp)") == "logic[4:0]");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::BadUnaryExpression);
    CHECK(diags[1].code == diag::BadBinaryExpression);
    CHECK(diags[2].code == diag::BadBinaryExpression);
    CHECK(diags[3].code == diag::BadConditionalExpression);
    CHECK(diags[4].code == diag::NotBooleanConvertible);
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
    always_comb asdf = asdf[foo:0];
    always_comb asdf = asdf[0+:foo];
    always_comb asdf = {foo {1}};
    always_comb asdf = foo'(1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExpressionNotConstant);
    CHECK(diags[1].code == diag::ExpressionNotConstant);
    CHECK(diags[2].code == diag::ExpressionNotConstant);
    CHECK(diags[3].code == diag::ExpressionNotConstant);
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
)",
                                     "source");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:7:17: warning: vector literal too large for the given number of bits [-Wliteral-overflow]
    int i = 35'd123498234978234;
                ^
source:8:13: error: size of vector literal cannot be zero
    int j = 0'd234;
            ^
source:9:13: error: size of vector literal is too large (> 16777215 bits)
    int k = 16777216'd1;
            ^
source:12:13: error: signed integer overflows 32 bits
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
source:21:17: warning: vector literal too large for the given number of bits [-Wliteral-overflow]
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
)",
                                     "source");

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

TEST_CASE("Crazy long hex literal") {
    std::string str = "int i = 'h";
    str += std::string(4194304, 'f');
    str += ';';

    auto tree = SyntaxTree::fromText(str);

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::LiteralSizeTooLarge);
}

// TODO: optimize and re-enable
// TEST_CASE("Crazy long decimal literal") {
//    std::string str = "int i = 'd";
//    str += std::string(5050446, '9');
//    str += ';';
//
//    auto tree = SyntaxTree::fromText(str);
//
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//
//    auto& diags = compilation.getAllDiagnostics();
//    REQUIRE(diags.size() == 1);
//    CHECK(diags[0].code == diag::LiteralSizeTooLarge);
//}
