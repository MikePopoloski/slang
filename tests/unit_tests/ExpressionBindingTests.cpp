#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SourceManager sourceManager;
BumpAllocator alloc;
Diagnostics diagnostics;

SyntaxTree parse(StringRef text) { return SyntaxTree::fromText(sourceManager, text); }

const ParameterInstanceSymbol& testParameter(std::string text, int index = 0) {
    auto tree = parse("module Top; " + text + " endmodule");

	SemanticModel sem(alloc, diagnostics);
	auto element = sem.bindDesignElement(tree.root()->members[0]->as<ModuleDeclarationSyntax>());
	REQUIRE(element);

	auto instance = sem.bindImplicitInstance(element);
	REQUIRE(instance);
	REQUIRE(instance->parameters.count() > (uint32_t)index);

	return *instance->parameters[index];
}

TEST_CASE("Bind parameter", "[binding:expressions]") {
    CHECK(get<SVInt>(testParameter("parameter foo = 4;").value) == 4);
	CHECK(get<SVInt>(testParameter("parameter foo = 4 + 5;").value) == 9);
	CHECK(get<SVInt>(testParameter("parameter bar = 9, foo = bar + 1;", 1).value) == 10);
}

}