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
module m;
    localparam int i = 5;
    localparam real r = 3.14;
    initial $display(i, r, "SDFSDF");
endmodule
)");

    CodeGenerator codegen(compilation);
    auto result = codegen.run(compilation.getRoot());

    CHECK("\n" + result == R"(
; ModuleID = 'primary'
source_filename = "primary"

@0 = private unnamed_addr constant [2 x i8] c"5\00", align 1
@1 = private unnamed_addr constant [5 x i8] c"3.14\00", align 1
@2 = private unnamed_addr constant [7 x i8] c"SDFSDF\00", align 1

define i32 @main() {
  %1 = call i32 @puts(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @0, i32 0, i32 0))
  %2 = call i32 @puts(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @1, i32 0, i32 0))
  %3 = call i32 @puts(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @2, i32 0, i32 0))
  ret i32 0
}

declare i32 @puts(i8*)
)");
}