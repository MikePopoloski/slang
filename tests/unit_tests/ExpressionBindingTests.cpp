#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SVInt testParameter(const std::string& text, int index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText<ModuleDeclarationSyntax>(StringRef(fullText));

    auto instance = SemanticModel(tree).makeImplicitInstance(
        tree.root()->as<ModuleDeclarationSyntax>());

    auto module = instance->module;
    REQUIRE(module);
    const auto* param = reinterpret_cast<const ParameterSymbol*>(
        module->scope->getNth(SymbolKind::Parameter, index));
    REQUIRE(param);

    if (!tree.diagnostics().empty())
        WARN(tree.reportDiagnostics());

    return param->value.integer();
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
    auto syntax = SyntaxTree::fromText<ExpressionSyntax>("i = i + 3");
    SemanticModel sem { syntax };

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root()->getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        sem.getKnownType(SyntaxKind::LogicType)
    };

    // Bind the expression tree to the symbol
    Scope scope;
    scope.add(&local);
    ExpressionBinder binder(sem, &scope);
    auto bound = binder.bindConstantExpression(syntax.root()->as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    // Initialize `i` to 1.
    ConstantEvaluator ce;
    auto& i = ce.createTemporary(&local);
    i = SVInt(1);

    // Evaluate the expression tree.
    ce.evaluate(bound);
    CHECK(i.integer() == 4);

    // Run it again, results should be as you'd expect
    ce.evaluate(bound);
    CHECK(i.integer() == 7);
}

TEST_CASE("Check type propagation", "[binding:expressions]") {
    // Assignment operator should increase RHS size to 20
    auto syntax = SyntaxTree::fromText<ExpressionSyntax>("i = 5'b0101 + 4'b1100");
    SemanticModel sem { syntax };

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root()->getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        sem.getIntegralType(20, false)
    };

    // Bind the expression tree to the symbol
    Scope scope;
    scope.add(&local);
    ExpressionBinder binder(sem, &scope);
    BoundExpression* bound = binder.bindConstantExpression(syntax.root()->as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound->type->width() == 20);
    BoundExpression* rhs = ((BoundAssignmentExpression *)bound)->right;
    CHECK(rhs->type->width() == 20);
    BoundExpression* op1 = ((BoundBinaryExpression *)rhs)->left;
    CHECK(op1->type->width() == 20);
    BoundExpression* op2 = ((BoundBinaryExpression *)rhs)->right;
    CHECK(op2->type->width() == 20);
}

TEST_CASE("Check type propagation 2", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText<ExpressionSyntax>("i = 2'b1 & (((17'b101 >> 1'b1) - 4'b1100) == 21'b1)");
    SemanticModel sem { syntax };

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root()->getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        sem.getIntegralType(20, false)
    };

    // Bind the expression tree to the symbol
    Scope scope;
    scope.add(&local);
    ExpressionBinder binder(sem, &scope);
    BoundExpression* bound = binder.bindConstantExpression(syntax.root()->as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound->type->width() == 20);
    BoundExpression* rhs = ((BoundAssignmentExpression *)bound)->right;
    CHECK(rhs->type->width() == 20);
    BoundExpression* rrhs = ((BoundAssignmentExpression *)rhs)->right;
    CHECK(rrhs->type->width() == 1);
    BoundExpression* op1 = ((BoundBinaryExpression *)rrhs)->left;
    BoundExpression* shiftExpr = ((BoundBinaryExpression *)op1)->left;
    CHECK(shiftExpr->type->width() == 17);
    CHECK(op1->type->width() == 17);
    BoundExpression* op2 = ((BoundBinaryExpression *)rrhs)->right;
    CHECK(op2->type->width() == 21);
}

TEST_CASE("Check type propagation real", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText<ExpressionSyntax>("i = 2'b1 & (((17'b101 >> 1'b1) - 2.0) == 21'b1)");
    SemanticModel sem { syntax };

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root()->getFirstToken();
    LocalVariableSymbol local {
        varToken.valueText(), varToken.location(),
        sem.getIntegralType(20, false)
    };

    // Bind the expression tree to the symbol
    Scope scope;
    scope.add(&local);
    ExpressionBinder binder(sem, &scope);
    BoundExpression* bound = binder.bindConstantExpression(syntax.root()->as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound->type->width() == 20);
    BoundExpression* rhs = ((BoundAssignmentExpression *)bound)->right;
    CHECK(rhs->type->width() == 20);
    BoundExpression* rrhs = ((BoundAssignmentExpression *)rhs)->right;
    CHECK(rrhs->type->width() == 1);
    BoundExpression* op1 = ((BoundBinaryExpression *)rrhs)->left;
    BoundExpression* shiftExpr = ((BoundBinaryExpression *)op1)->left;
    CHECK(shiftExpr->type->width() == 64);
    CHECK(shiftExpr->type->isReal());
    BoundExpression* rshiftOp = ((BoundBinaryExpression *)shiftExpr)->right;
    CHECK(rshiftOp->type->width() == 1);
    BoundExpression* lshiftOp = ((BoundBinaryExpression *)shiftExpr)->left;
    CHECK(lshiftOp->type->width() == 17);
    CHECK(op1->type->width() == 64);
    CHECK(op1->type->isReal());
    BoundExpression* op2 = ((BoundBinaryExpression *)rrhs)->right;
    CHECK(op2->type->width() == 21);
}

}
