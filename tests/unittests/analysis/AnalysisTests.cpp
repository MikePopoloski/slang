// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

class TestAnalysis : public AbstractFlowAnalysis<TestAnalysis, int> {
public:
    TestAnalysis(const Symbol& symbol) : AbstractFlowAnalysis(symbol, AnalysisFlags::None) {}

    void handle(const NamedValueExpression& expr) {
        getState() += 1;
        visitExpr(expr);
    }

    void joinState(int& state, const int& other) const { state += other; }
    void meetState(int& state, const int& other) const { state = std::min(state, other); }
    int copyState(const int& state) const { return state; }
    int unreachableState() const { return 0; }
    int topState() const { return 0; }

    int getCurrentState() const { return getState(); }
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

    TestAnalysis analysis(proc);
    analysis.run(proc.getBody());
    CHECK(!analysis.bad);
    CHECK(analysis.getCurrentState() == 5);
}

TEST_CASE("Inferred latch test") {
    auto& code = R"(
module m(input clk, input rst, input [2:0] in, output logic out);
    struct { logic a; logic b; } s;
    always_comb begin
        if (rst) begin
            s.a = 0;
            s.b = 0;
        end
        else begin
            s.a = 1;
        end
    end

    always_comb begin
        case(in[1:0])
            2'b00:  out = 1'b0;
            2'b01:  out = 1'b1;
            2'b10:  out = 1'b1;
            // inferred latch "out" :: missing condition 2'b11/default
        endcase
    end

    logic flop0, flop1, flop2, flop3;
    logic next0, next1, next2, next3;
    logic b,c;

    always_comb begin
        next0 = flop0;
        next1 = flop1;
        // inferred latch "next2" :: missing initial condition
        next3 = flop3;
        case(in[2:0])
            3'b001:             next0 = in[0];
            3'b010:  if(b)      next1 = in[0];
            3'b100:  if(c)      next2 = in[0];
            default: if(!b&&!c) next3 = in[0];
        endcase
    end

    parameter p = 4;
    logic [p-1:0] slots;
    logic q,r,t;
    always_comb begin
        for (int i = 0; i < p; i++) begin
            if (b) slots[i] = 1;
            else   slots[i] = 0;
        end

        for (;;) begin
            q = 1;
            break;
        end

        forever begin
            r = 1;
            break;
            t = 1;
        end
    end

    logic u, v;
    always_comb begin
        while (0) begin
            u = 1;
        end
        while (1) begin
            v = 1;
            break;
        end
    end

    I iface();
    n n1(iface);

    typedef enum logic [2:0] {
        A, B, C, D,
        E, F, G, H
    } e_t;

    e_t e;
    logic x;

    always_comb begin
        case (e)
            A, B, C, D: x = 1'b1;
            default: x = 1'b0;
        endcase
    end
endmodule

interface I;
    logic a;
    modport m(output a);
endinterface

module n(I.m i);
    always_comb begin
        i.a = 1;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InferredLatch);
    CHECK(diags[1].code == diag::InferredLatch);
    CHECK(diags[2].code == diag::InferredLatch);
}

TEST_CASE("Inferred latches with 4-state case statements") {
    auto& code = R"(
module m;
    logic [2:0] a;
    logic b;
    int c, d, e;

    always_comb begin
        case (b)
            0: c = 1;
            1: c = 1;
            1'bx: c = 1;
            1'bz: c = 1;
        endcase
    end

    always_comb begin
        casez (a)
            3'b000: d = 1;
            3'b001: d = 1;
            3'b01?: d = 1;
            3'b0x?: d = 1;
            3'b0z?: d = 1;
            3'b1??: d = 1;
            3'bx??: d = 1;
            3'bz??: d = 1;
        endcase
    end

    always_comb begin
        unique case (b)
            1'b0: e = 1;
            1'b1: e = 1;
        endcase
    end
endmodule
)";

    AnalysisOptions options;
    options.flags = AnalysisFlags::FullCaseFourState | AnalysisFlags::FullCaseUniquePriority;

    Compilation compilation;
    AnalysisManager analysisManager(options);

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Inferred latches with 2-state case statements") {
    auto& code = R"(
module m;
    logic [2:0] a;
    logic b;
    int c, d, e, f, g;
    logic signed [1:0] h;

    always_comb begin
        case (b)
            1'b0: c = 1;
            1'b1: c = 1;
        endcase
    end

    always_comb begin
        casex (a)
            3'b000: d = 1;
            3'b001: d = 1;
            3'b01?: d = 1;
            3'b1??: d = 1;
        endcase
    end

    always_comb begin
        casex (a)
            3'b000: e = 1;
            3'b001: e = 1;
            3'b010: e = 1;
            3'b1??: e = 1;
        endcase
    end

    always_comb begin
        case (b)
            0: f = 1;
        endcase

        case (h)
            -2: g = 1;
            -1: g = 1;
            0:  g = 1;
            1:  g = 1;
        endcase
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InferredLatch);
    CHECK(diags[1].code == diag::InferredLatch);
}

TEST_CASE("Inferred latch warning correct LSP in message") {
    auto& code = R"(
module m;
    struct packed { int a; int b; } s;
    logic c;

    always_comb begin
        if (c) begin
            s.a = 1;
            s.b[0] = 1;
            s.b[1] = 1;
        end
        else begin
            s[0] = 1;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:8:13: warning: latch inferred for 's.a' because it is not assigned on all control paths [-Winferred-latch]
            s.a = 1;
            ^~~
source:10:13: warning: latch inferred for 's.b[1]' because it is not assigned on all control paths [-Winferred-latch]
            s.b[1] = 1;
            ^~~~~~
)");
}

TEST_CASE("Data flow with class members") {
    auto& code = R"(
class C;
    int i;
endclass

function C foo;
endfunction

module m(input a);
    C c;
    always_comb begin
        if (a) begin
            foo().i = 1;
            foo().i = 2;
            c.i = 3;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}
