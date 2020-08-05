#include "Test.h"

#include "slang/codegen/JIT.h"
#include "slang/runtime/Runtime.h"
#include "slang/symbols/BlockSymbols.h"

TEST_CASE("JIT test") {
    Compilation compilation = compile(R"(
module m;
    initial begin
        automatic int i = 4;
        $display(3, i, , "Hello, World!");
    end
endmodule
)");

    auto& block =
        *compilation.getRoot().topInstances[0]->body.membersOfType<ProceduralBlockSymbol>()[0];

    MIRBuilder builder(compilation);
    Procedure proc(builder, block);

    CodeGenerator codegen(compilation);
    codegen.emit(proc);

    std::string result;
    slang::runtime::setOutputHandler([&](string_view text) { result += text; });

    JIT jit;
    jit.addCode(codegen.finish());
    CHECK(jit.run() == 0);

    CHECK(result == "          3          4 Hello, World!\n");
}