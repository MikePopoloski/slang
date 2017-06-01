#include "Catch/catch.hpp"

#include "analysis/Binder.h"
#include "analysis/ConstantEvaluator.h"
#include "parsing/SyntaxTree.h"

using namespace slang;

namespace {

SVInt testParameter(const std::string& text, int index = 0) {
    const auto& fullText = "module Top; " + text + " endmodule";
    auto tree = SyntaxTree::fromText(StringRef(fullText));

	DesignRootSymbol root(tree);
	const auto& instance = root.lookup("Top")->as<ModuleInstanceSymbol>();
	if (!tree.diagnostics().empty())
		WARN(tree.reportDiagnostics());

    const auto& module = instance.module;
	const ParameterSymbol& param = module.member<ParameterSymbol>(index);

    return param.value.integer();
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
	DesignRootSymbol root;

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
		root.getKnownType(SyntaxKind::LogicType), root
    };

    // Bind the expression tree to the symbol
    root.addMember(local);
    Binder binder(root);
    const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    // Initialize `i` to 1.
    ConstantEvaluator ce;
    auto& i = ce.createTemporary(local);
    i = SVInt(1);

    // Evaluate the expression tree.
    ce.evaluateExpr(bound);
    CHECK(i.integer() == 4);

    // Run it again, results should be as you'd expect
    ce.evaluateExpr(bound);
    CHECK(i.integer() == 7);
}

TEST_CASE("Check type propagation", "[binding:expressions]") {
    // Assignment operator should increase RHS size to 20
    auto syntax = SyntaxTree::fromText("i = 5'b0101 + 4'b1100");
	DesignRootSymbol root;

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        root.getIntegralType(20, false), root
    };

    // Bind the expression tree to the symbol
	root.addMember(local);
	Binder binder(root);
	const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const BoundExpression& rhs = ((const BoundAssignmentExpression&)bound).right;
    CHECK(rhs.type->width() == 20);
    const BoundExpression& op1 = ((const BoundBinaryExpression&)rhs).left;
    CHECK(op1.type->width() == 20);
    const BoundExpression& op2 = ((const BoundBinaryExpression&)rhs).right;
    CHECK(op2.type->width() == 20);
}

TEST_CASE("Check type propagation 2", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 4'b1100) == 21'b1)");
	DesignRootSymbol root;

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        root.getIntegralType(20, false), root
    };

    // Bind the expression tree to the symbol
	root.addMember(local);
	Binder binder(root);
	const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const BoundExpression& rhs = ((const BoundAssignmentExpression&)bound).right;
    CHECK(rhs.type->width() == 20);
    const BoundExpression& rrhs = ((const BoundAssignmentExpression&)rhs).right;
    CHECK(rrhs.type->width() == 1);
    const BoundExpression& op1 = ((const BoundBinaryExpression&)rrhs).left;
    const BoundExpression& shiftExpr = ((const BoundBinaryExpression&)op1).left;
    CHECK(shiftExpr.type->width() == 17);
    CHECK(op1.type->width() == 17);
    const BoundExpression& op2 = ((const BoundBinaryExpression&)rrhs).right;
    CHECK(op2.type->width() == 21);
}

TEST_CASE("Check type propagation real", "[binding:expressions]") {
    // Tests a number of rules of size propogation
    auto syntax = SyntaxTree::fromText("i = 2'b1 & (((17'b101 >> 1'b1) - 2.0) == 21'b1)");
	DesignRootSymbol root;

    // Fabricate a symbol for the `i` variable
    auto varToken = syntax.root().getFirstToken();
    VariableSymbol local {
        varToken.valueText(), varToken.location(),
        root.getIntegralType(20, false), root
    };

    // Bind the expression tree to the symbol
	root.addMember(local);
	Binder binder(root);
	const auto& bound = binder.bindConstantExpression(syntax.root().as<ExpressionSyntax>());
    REQUIRE(syntax.diagnostics().empty());

    CHECK(bound.type->width() == 20);
    const BoundExpression& rhs = ((const BoundAssignmentExpression&)bound).right;
    CHECK(rhs.type->width() == 20);
    const BoundExpression& rrhs = ((const BoundAssignmentExpression&)rhs).right;
    CHECK(rrhs.type->width() == 1);
    const BoundExpression& op1 = ((const BoundBinaryExpression&)rrhs).left;
    const BoundExpression& shiftExpr = ((const BoundBinaryExpression&)op1).left;
    CHECK(shiftExpr.type->width() == 64);
    CHECK(shiftExpr.type->isReal());
    const BoundExpression& rshiftOp = ((const BoundBinaryExpression&)shiftExpr).right;
    CHECK(rshiftOp.type->width() == 1);
    const BoundExpression& lshiftOp = ((const BoundBinaryExpression&)shiftExpr).left;
    CHECK(lshiftOp.type->width() == 17);
    CHECK(op1.type->width() == 64);
    CHECK(op1.type->isReal());
    const BoundExpression& op2 = ((const BoundBinaryExpression&)rrhs).right;
    CHECK(op2.type->width() == 21);
}

}
