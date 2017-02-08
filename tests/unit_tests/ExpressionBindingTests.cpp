#include "Catch/catch.hpp"
#include "slang.h"

#include "HashMap.h"

using namespace slang;

namespace {

SourceManager sourceManager;
BumpAllocator alloc;
DiagnosticWriter diagWriter(sourceManager);

SyntaxTree parse(const std::string& text) { return SyntaxTree::fromText(sourceManager, StringRef(text)); }

SVInt testParameter(const std::string& text, int index = 0) {
    auto tree = parse("module Top; " + text + " endmodule");

    Diagnostics& diagnostics = tree.diagnostics();
    DeclarationTable declTable(diagnostics);
    declTable.addSyntaxTree(&tree);

    SemanticModel sem(alloc, diagnostics, declTable);
    auto instance = sem.makeImplicitInstance(tree.root()->members[0]->as<ModuleDeclarationSyntax>());
    auto module = instance->module;
    REQUIRE(module);
    const auto* param = reinterpret_cast<const ParameterSymbol*>(
        module->scope->getNth(SymbolKind::Parameter, index));
    REQUIRE(param);

    if (!diagnostics.empty())
        WARN(diagWriter.report(diagnostics).c_str());

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
