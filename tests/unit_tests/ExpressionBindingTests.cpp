#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SourceManager sourceManager;
BumpAllocator alloc;
DiagnosticWriter diagWriter(sourceManager);

SyntaxTree parse(const std::string& text) { return SyntaxTree::fromText(sourceManager, StringRef(text)); }

const ParameterSymbol& testParameter(const std::string& text, int index = 0) {
    auto tree = parse("module Top; " + text + " endmodule");

    Diagnostics& diagnostics = tree.diagnostics();
    SemanticModel sem(alloc, diagnostics);
    auto instance = sem.makeImplicitInstance(tree.root()->members[0]->as<ModuleDeclarationSyntax>());
    REQUIRE(instance);
    REQUIRE(instance->bodyParameters.count() > (uint32_t)index);

    if (!diagnostics.empty())
        WARN(diagWriter.report(diagnostics).c_str());

    return *instance->bodyParameters[index];
}

TEST_CASE("Bind parameter", "[binding:expressions]") {
    CHECK(std::get<SVInt>(testParameter("parameter foo = 4;").value) == 4);
    CHECK(std::get<SVInt>(testParameter("parameter foo = 4 + 5;").value) == 9);
    CHECK(std::get<SVInt>(testParameter("parameter bar = 9, foo = bar + 1;", 1).value) == 10);
    CHECK(std::get<SVInt>(testParameter("parameter logic [3:0] foo = 4;").value) == 4);
    CHECK(std::get<SVInt>(testParameter("parameter logic [3:0] foo = 4'b100;").value) == 4);
    CHECK(std::get<SVInt>(testParameter("parameter foo = |3.14159;").value) == 4);
}

}