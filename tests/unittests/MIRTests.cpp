#include "Test.h"

#include "slang/mir/MIRBuilder.h"
#include "slang/mir/MIRPrinter.h"
#include "slang/mir/Procedure.h"

using namespace slang::mir;

TEST_CASE("MIR -- basic test") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int j = 4;
    initial begin : block
        automatic int i = 1;
        $display(i, , "hello %0d world", j);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& block =
        *compilation.getRoot().topInstances[0]->body.membersOfType<ProceduralBlockSymbol>()[0];

    MIRBuilder builder(compilation);
    Procedure proc(builder, block);

    MIRPrinter printer(builder);
    printer.printGlobals();
    printer.str().append("\n");
    printer.print(proc);

    std::string result = "\n" + printer.str();
    CHECK(result == R"(
G0 j: int

L0 i: int
%0 = syscall $printInt L0, 8'h2: bit[7:0], 32'd0: bit[31:0], 1'b0: bit[0:0]
%1 = syscall $printChar 8'h20: bit[7:0]
%2 = syscall $printStringLit hello : string
%3 = syscall $printInt G0[j], 8'h2: bit[7:0], 32'd0: bit[31:0], 1'b1: bit[0:0]
%4 = syscall $printStringLit  world: string
)");
}