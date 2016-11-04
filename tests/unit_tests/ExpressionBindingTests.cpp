#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

SourceManager sourceManager;

SyntaxTree parse(StringRef text) {
    return SyntaxTree::fromText(sourceManager, text);
}

//BoundParameterDeclaration* testParameter(SemanticModel& sem, std::string text) {
//    auto tree = parse("module Top; " + text + " endmodule");
//    auto paramDecl = tree.root()->members[0]->as<ModuleDeclarationSyntax>()->members[0]->as<ParameterDeclarationStatementSyntax>();
//
//    auto parameter = sem.bindParameterDecl(paramDecl->parameter->as<ParameterDeclarationSyntax>());
//    REQUIRE(parameter);
//    return parameter;
//}
//
//TEST_CASE("Bind parameter", "[binding:expressions]") {
//    SemanticModel sem;
//
//    CHECK(get<SVInt>(testParameter(sem, "parameter foo = 4;")->value) == 4);
//    CHECK(get<SVInt>(testParameter(sem, "parameter foo = 4 + 5;")->value) == 9);
//}

}