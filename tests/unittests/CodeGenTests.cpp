// This file contains basic tests for LLVM code generation.
// NOTE: It is only included in the build when the SLANG_INCLUDE_LLVM cmake
// option is enabled. Otherwise the tests won't be built or run.
#include <catch2/catch.hpp>

#include "slang/codegen/CodeGenerator.h"
#include "slang/codegen/JIT.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/mir/MIRBuilder.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;
using namespace slang::mir;

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
    auto result = codegen.finish().toString();

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

TEST_CASE("JIT test") {
    Compilation compilation = compile(R"(
module m;
    initial $display(,);
endmodule
)");

    auto& block =
        *compilation.getRoot().topInstances[0]->body.membersOfType<ProceduralBlockSymbol>()[0];

    MIRBuilder builder(compilation);
    Procedure proc(builder, block);

    CodeGenerator codegen(compilation);
    codegen.generate(proc);

    JIT jit;
    jit.addCode(codegen.finish());
    CHECK(jit.run() == 0);
}