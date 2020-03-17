// This file contains basic tests for LLVM code generation.
// NOTE: It is only included in the build when the SLANG_INCLUDE_LLVM cmake
// option is enabled. Otherwise the tests won't be built or run.
#include <catch2/catch.hpp>

#include "slang/codegen/CodeGenerator.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/DefinitionSymbols.h"
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
module m;
    localparam int i = 5;
    int r = 3;
    initial $display(i, r, "SDFSDF");
endmodule
)");

    CodeGenerator codegen(compilation);
    codegen.genInstance(*compilation.getRoot().topInstances[0]);
    auto result = codegen.finish();

    CHECK("\n" + result == R"(
; ModuleID = 'primary'
source_filename = "primary"

@0 = private global i32 3

define i32 @main() {
  br label %1

1:                                                ; preds = %0
  ret i32 0
}
)");
}