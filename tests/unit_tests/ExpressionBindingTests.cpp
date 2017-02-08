#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SVInt testParameter(const std::string& text, int index = 0) {
    StringRef fullText { "module Top; " + text + " endmodule" };
    auto tree = SyntaxTree::fromText<ModuleDeclarationSyntax>(fullText);

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
    LocalVariableSymbol local {
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

}
