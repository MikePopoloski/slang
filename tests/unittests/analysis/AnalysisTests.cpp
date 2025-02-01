// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/analysis/AbstractFlowAnalysis.h"

class TestAnalysis : public analysis::AbstractFlowAnalysis<TestAnalysis, int> {
public:
    TestAnalysis(const Symbol& symbol, const Statement& stmt) :
        AbstractFlowAnalysis(symbol, stmt) {}

    void handle(const NamedValueExpression& expr) {
        state++;
        visitExpr(expr);
    }

    void joinState(int& state, const int& other) const { state += other; }
    int unreachableState() const { return 0; }
    int topState() const { return 0; }

    int getState() const { return state; }
};

TEST_CASE("Basic flow analysis") {
    auto tree = SyntaxTree::fromText(R"(
module m(input clk, input rst, output logic a, input logic b);
    always @(posedge clk) begin
        if (rst)
            a <= 0;
        else
            a <= b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& m = compilation.getRoot().topInstances[0]->body;
    auto& proc = m.membersOfType<ProceduralBlockSymbol>().front();

    TestAnalysis analysis(proc, proc.getBody());
    CHECK(!analysis.bad);
    CHECK(analysis.getState() == 5);
}
