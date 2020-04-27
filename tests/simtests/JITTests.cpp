#include "Test.h"

#include "slang/codegen/JIT.h"
#include "slang/symbols/BlockSymbols.h"

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