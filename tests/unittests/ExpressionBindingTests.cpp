#include "Test.h"

#include "analysis/Binder.h"
#include "analysis/RootSymbol.h"
#include "parsing/SyntaxTree.h"

SVInt testParameter(const std::string& text, int index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(string_view(fullText));

    RootSymbol root(&tree);
    const auto& module = *root.topInstances()[0];
    if (!tree.diagnostics().empty())
        WARN(tree.reportDiagnostics());

    const ParameterSymbol& param = module.member<ParameterSymbol>(index);
    return param.value->integer();
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
    RootSymbol root(syntax.sourceManager());
    DynamicScopeSymbol scope(root);

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local {varToken.valueText(), scope};
    local.type = root.factory.getIntType();

    // Bind the expression tree to the symbol
    scope.addSymbol(local);
    Binder binder(scope, LookupKind::Direct);
    const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    // Initialize `i` to 1.
    EvalContext context;
    auto i = context.createLocal(&local, { root.factory.getIntType(), SVInt(1) });

    // Evaluate the expression tree.
    bound.eval(context);
    CHECK(i->integer() == 4);

    // Run it again, results should be as you'd expect
    bound.eval(context);
    CHECK(i->integer() == 7);
}

TEST_CASE("Check type propagation", "[binding:expressions]") {
    // Assignment operator should increase RHS size to 20
    auto syntax = SyntaxTree::fromText("i = 5'b0101 + 4'b1100");
    RootSymbol root(syntax.sourceManager());
    DynamicScopeSymbol scope(root);
    
    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), scope };
    local.type = root.factory.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addSymbol(local);
    Binder binder(scope, LookupKind::Direct);
    const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->width() == 20);
    const Expression& op1 = rhs.as<BinaryExpression>().left();
    CHECK(op1.type->width() == 20);
    const Expression& op2 = rhs.as<BinaryExpression>().right();
    CHECK(op2.type->width() == 20);
}

TEST_CASE("Check type propagation 2", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 4'b1100) == 21'b1)");
    RootSymbol root(syntax.sourceManager());
    DynamicScopeSymbol scope(root);

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), scope };
    local.type = root.factory.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addSymbol(local);
    Binder binder(scope, LookupKind::Direct);
    const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->width() == 20);
    const Expression& rrhs = rhs.as<BinaryExpression>().right();
    CHECK(rrhs.type->width() == 1);
    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const Expression& shiftExpr = op1.as<BinaryExpression>().left();
    CHECK(shiftExpr.type->width() == 17);
    CHECK(op1.type->width() == 17);
    const Expression& op2 = rrhs.as<BinaryExpression>().right();
    CHECK(op2.type->width() == 21);
}

TEST_CASE("Check type propagation real", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 2.0) == 21'b1)");
    RootSymbol root(syntax.sourceManager());
    DynamicScopeSymbol scope(root);

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local { varToken.valueText(), scope };
    local.type = root.factory.getType(20, false);

    // Bind the expression tree to the symbol
    scope.addSymbol(local);
    Binder binder(scope, LookupKind::Direct);
    const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const Expression& rhs = bound.as<BinaryExpression>().right();
    CHECK(rhs.type->width() == 20);
    const Expression& rrhs = rhs.as<BinaryExpression>().right();
    CHECK(rrhs.type->width() == 1);
    const Expression& op1 = rrhs.as<BinaryExpression>().left();
    const Expression& shiftExpr = op1.as<BinaryExpression>().left();
    CHECK(shiftExpr.type->width() == 64);
    CHECK(shiftExpr.type->isReal());
    const Expression& rshiftOp = shiftExpr.as<BinaryExpression>().right();
    CHECK(rshiftOp.type->width() == 1);
    const Expression& lshiftOp = shiftExpr.as<BinaryExpression>().left();
    CHECK(lshiftOp.type->width() == 17);
    CHECK(op1.type->width() == 64);
    CHECK(op1.type->isReal());
    const Expression& op2 = rrhs.as<BinaryExpression>().right();
    CHECK(op2.type->width() == 21);
}
