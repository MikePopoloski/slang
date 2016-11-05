#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SourceManager sourceManager;
BumpAllocator alloc;
Diagnostics diagnostics;

SyntaxTree parse(StringRef text) { return SyntaxTree::fromText(sourceManager, text); }

const ParameterInstance& testParameter(std::string text) {
    auto tree = parse("module Top; " + text + " endmodule");

	SemanticModel sem(alloc, diagnostics);
	auto element = sem.bindDesignElement(tree.root()->members[0]->as<ModuleDeclarationSyntax>());
	REQUIRE(element);

	auto instance = sem.bindImplicitInstance(element);
	REQUIRE(instance);
	REQUIRE(instance->parameters.count() > 0);

	return instance->parameters[0];
}

TEST_CASE("Bind parameter", "[binding:expressions]") {
    CHECK(get<SVInt>(testParameter("parameter foo = 4;").value) == 4);
    CHECK(get<SVInt>(testParameter("parameter foo = 4 + 5;").value) == 9);
}

}