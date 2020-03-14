// This file contains basic tests for LLVM code generation.
// NOTE: It is only included in the build when the SLANG_INCLUDE_LLVM cmake
// option is enabled. Otherwise the tests won't be built or run.
#include <catch2/catch.hpp>

#include "slang/codegen/CodeGenerator.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;

Compilation compile(const std::string& text) {
    Compilation compilation;
    compilation.addSyntaxTree(SyntaxTree::fromText(text));

    auto& diags = compilation.getAllDiagnostics();
    if (!diags.empty()) {
        std::string report =
            DiagnosticEngine::reportAll(SyntaxTree::getDefaultSourceManager(), diags);
        FAIL_CHECK(report);
    }

    return compilation;
}

TEST_CASE("Basic test") {
    Compilation compilation = compile(R"(
)");

    CodeGenerator codegen;
    auto result = codegen.run(compilation.getRoot());

    CHECK("\n" + result == R"(
; ModuleID = 'primary'
source_filename = "primary"

define i32 @main() {
  ret i32 0
}
)");
}