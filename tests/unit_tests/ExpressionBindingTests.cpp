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

}
