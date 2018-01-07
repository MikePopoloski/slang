#include "Test.h"

#include "compilation/Compilation.h"
#include "parsing/SyntaxTree.h"

SVInt testParameter(const std::string& text, uint32_t index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(string_view(fullText));

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    const auto& module = *compilation.getRoot().topInstances[0];
    if (!tree.diagnostics().empty())
        WARN(tree.reportDiagnostics());

    const ParameterSymbol& param = module.memberAt<ParameterSymbol>(index);
    return param.getValue().integer();
}

TEST_CASE("Bind parameter", "[binding:expressions]") {
    CHECK(testParameter("parameter foo = 4;") == 4);
    CHECK(testParameter("parameter foo = 4 + 5;") == 9);
    CHECK(testParameter("parameter bar = 9, foo = bar + 1;", 1) == 10);
    CHECK(testParameter("parameter logic [3:0] foo = 4;") == 4);
    CHECK(testParameter("parameter logic [3:0] foo = 4'b100;") == 4);
}

TEST_CASE("Evaluate assignment expression", "[binding:expressions") {
    // Evaluate an assignment expression (has an LValue we can observe)
    auto syntax = SyntaxTree::fromText("i = i + 3");

    // Fabricate a symbol for the `i` variable
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), varToken.location() };
    local.type = compilation.getIntType();

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = compilation.bindExpression(syntax.root().as<ExpressionSyntax>(), scope);
    REQUIRE(syntax.diagnostics().empty());

    // Initialize `i` to 1.
    EvalContext context;
    auto i = context.createLocal(&local, SVInt(1));

    // Evaluate the expression tree.
    bound.eval(context);
    CHECK(i->integer() == 4);

    // Run it again, results should be as you'd expect
    bound.eval(context);
    CHECK(i->integer() == 7);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation", "[binding:expressions]") {
    // Assignment operator should increase RHS size to 20
    auto syntax = SyntaxTree::fromText("i = 5'b0101 + 4'b1100");

    // Fabricate a symbol for the `i` variable
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), varToken.location() };
    local.type = compilation.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = compilation.bindExpression(syntax.root().as<ExpressionSyntax>(), scope);
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->getBitWidth() == 20);
    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);
    const Expression& op1 = rhs.as<BinaryExpression>().left();
    CHECK(op1.type->getBitWidth() == 20);
    const Expression& op2 = rhs.as<BinaryExpression>().right();
    CHECK(op2.type->getBitWidth() == 20);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation 2", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 4'b1100) == 21'b1)");
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), varToken.location() };
    local.type = compilation.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = compilation.bindExpression(syntax.root().as<ExpressionSyntax>(), scope);
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->getBitWidth() == 20);
    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);

    const Expression& rrhs = rhs.as<BinaryExpression>().right();
    CHECK(rrhs.type->getBitWidth() == 1);

    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const Expression& shiftExpr = op1.as<BinaryExpression>().left();
    CHECK(shiftExpr.type->getBitWidth() == 21);
    CHECK(op1.type->getBitWidth() == 21);
    const Expression& op2 = rrhs.as<BinaryExpression>().right();
    CHECK(op2.type->getBitWidth() == 21);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Check type propagation real", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 2.0) == 21'b1)");
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), varToken.location() };
    local.type = compilation.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addMember(local);
    const auto& bound = compilation.bindExpression(syntax.root().as<ExpressionSyntax>(), scope);
    REQUIRE(syntax.diagnostics().empty());
    CHECK(bound.type->getBitWidth() == 20);

    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->getBitWidth() == 20);

    const Expression& rrhs = rhs.as<BinaryExpression>().right();
    CHECK(rrhs.type->getBitWidth() == 1);

    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const ConversionExpression& convExpr = op1.as<BinaryExpression>().left().as<ConversionExpression>();
    CHECK(convExpr.type->getBitWidth() == 64);
    CHECK(convExpr.type->isFloating());
    CHECK(convExpr.conversionKind == ConversionKind::IntToFloat);

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
