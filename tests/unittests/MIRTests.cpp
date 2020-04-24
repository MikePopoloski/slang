#include "Test.h"

#include "slang/mir/MIRBuilder.h"
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

    std::string result = "\n" + proc.toString();
    CHECK(result == R"(
%0 = syscall $printChar 8'h20
)");
}