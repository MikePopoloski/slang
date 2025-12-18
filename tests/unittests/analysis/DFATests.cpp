// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

#include "slang/analysis/DataFlowAnalysis.h"

class TestAnalysis : public AbstractFlowAnalysis<TestAnalysis, int> {
public:
    TestAnalysis(const Symbol& symbol) : AbstractFlowAnalysis(symbol, {}) {}

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

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InferredLatch);
    CHECK(diags[1].code == diag::InferredLatch);
    CHECK(diags[2].code == diag::InferredLatch);
    CHECK(diags[3].code == diag::CaseEnumExplicit);
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

    auto diags = analyze(code, compilation, analysisManager);
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
    return null;
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

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Data flow with constants in repeat, randcase, foreach") {
    auto& code = R"(
module m;
    int i, j, k, l, n, o, p;
    int d[3][][2];
    logic [1:0] e[2][1];
    always_comb begin
        repeat (1) begin
            i = 1;
        end

        randcase
            0: ;
            1: j = 1;
        endcase

        randcase
            2: k = 1;
            1: k = 1;
        endcase

        randcase
            0: l = 1;
            0: l = 2;
        endcase

        foreach (d[a, b, c]) begin
            n = 1;
        end

        foreach (d[a, , c]) begin
            o = 1;
        end

        foreach (e[a, b, c]) begin
            p = 1;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InferredLatch);
}

TEST_CASE("Functions with missing returns") {
    auto& code = R"(
function int foo;
endfunction

function int bar(input a);
    if (a) begin
        return 1;
    end
endfunction

function int baz;
    while (1) begin
        return 1;
    end
endfunction

function int boz(input a);
    if (a) begin
        return 1;
    end
    boz = 2;
endfunction

function int fiz(input a);
    if (a) begin
        fiz = 1;
    end
endfunction
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MissingReturn);
    CHECK(diags[1].code == diag::IncompleteReturn);
    CHECK(diags[2].code == diag::IncompleteReturn);
}

TEST_CASE("Unevaluated syscall args don't contribute to data flow") {
    auto& code = R"(
module m;
    int i, j;
    always_comb begin
        if (i) begin
            i = 1;
            j = 2;
        end
        else begin
            j = $bits((i = 2));
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InferredLatch);
}

TEST_CASE("Analysis with syscalls that never return") {
    auto& code = R"(
function int foo(int i);
    if (i == 0)
        return 1;
    else if (i == 1)
        return 2;
    else
        $fatal();
endfunction
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("For loop analysis crash regress -- GH #1292") {
    auto& code = R"(
module Test (
  input  logic clk,
  input  logic in,
  output logic out
);

  logic internal[4];

  assign internal[0] = in;
  assign out = internal[3];

  always_ff @(posedge clk) begin
    internal[1] <= internal[0];
    for (int stage = 2; stage <= 3; stage++) begin
      internal[stage] <= internal[stage-1];
    end
  end

endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Latch with conditions inside loop regress -- GH #1364") {
    auto& code = R"(
module Test;
  logic [3:0][31:0] a;

  always_comb begin
    for (int i = 0; i < 4; i++) begin
      if (i == 0) begin
        a[i] = 0;
      end
      else if (i == 1) begin
        a[i] = 1;
      end
      else if (i == 2) begin
        a[i] = 2;
      end
      else if (i == 3) begin
        a[i] = 3;
      end
    end
  end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("No latch inferred for always_latch") {
    auto& code = R"(
module m(input clk, input rst, input [2:0] in, output logic out, output logic out1);
    struct { logic a; logic b; } s, s1;
    always_latch begin
        if (rst) begin
            s.a = 0;
            s.b = 0;
        end
        else begin
            s.a = 1;
            s.b = 0;
        end
    end
    always_latch begin
        if (rst) begin
            s1.a = 0;
            s1.b = 0;
        end
        // inferred latches on "s1.a" and "s1.b" :: missing else branch
    end
    always_latch begin
        case(in[1:0])
            2'b00:  out1 = 1'b0;
            2'b01:  out1 = 1'b1;
            2'b10:  out1 = 1'b1;
            // inferred latch "out" :: missing condition 2'b11/default
        endcase
    end
    always_latch begin
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
    always_latch begin
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
    always_latch begin
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
    always_latch begin
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
    always_latch begin
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
    always_latch begin
        i.a = 1;
    end
endmodule
module test10(out);
  output reg [2:0] out;
  reg en;
  always_latch begin
    out[1] <= 1;
    case (en)
      2'b00 : out[1] <= 1'b1;
      2'b10 : out[2] <= 1'b1;
      default : ;
    endcase
  end
endmodule // test
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 13);
    CHECK(diags[0].code == diag::InferredComb);
    CHECK(diags[1].code == diag::InferredComb);
    CHECK(diags[2].code == diag::InferredComb);
    CHECK(diags[3].code == diag::InferredComb);
    CHECK(diags[4].code == diag::InferredComb);
    CHECK(diags[5].code == diag::InferredComb);
    CHECK(diags[6].code == diag::InferredComb);
    CHECK(diags[7].code == diag::InferredComb);
    CHECK(diags[8].code == diag::InferredComb);
    CHECK(diags[9].code == diag::CaseEnumExplicit);
    CHECK(diags[10].code == diag::InferredComb);
    CHECK(diags[11].code == diag::InferredComb);
    CHECK(diags[12].code == diag::InferredComb);
}

TEST_CASE("DFA with missing function call error -- GH #1426") {
    auto& code = R"(
function reg foo0(reg q);
    return bar(q);
endfunction
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto tree = SyntaxTree::fromText(code);
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    compilation.freeze();

    analysisManager.analyze(compilation);
    auto diags = analysisManager.getDiagnostics();
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Always without timing control analysis") {
    auto& code = R"(
module timing_test;
    logic clk, a, b, c;
    // This should trigger AlwaysWithoutTimingControl
    always begin
        a = b;
    end
    // This should be fine (has timing control)
    always @(posedge clk) begin
        b = a;
    end
    // This should trigger it (assertion doesn't count as timing control)
    always begin
        assert property (@(posedge clk) a |=> b);
    end
    // Test subroutine calls
    function void my_func();
        // No timing control in function
    endfunction
    task my_task();
        @(posedge clk);  // Has timing control
    endtask
    task my_task_2();
        my_task();
    endtask
    // This should be fine (calls task which calls task with timing)
    always begin
        my_task_2();
    end
    // This should trigger diagnostic (calls function without timing)
    always begin
        my_func();
    end
    // This should be fine (calls task with timing)
    always begin
        my_task();
    end
    // Test with wait statements (should be valid)
    always begin
        wait(clk);
        c = a;
    end
    // Test with delay control (should be valid)
    always begin
        #10 c = b;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::AlwaysWithoutTimingControl);
    CHECK(diags[1].code == diag::AlwaysWithoutTimingControl);
    CHECK(diags[2].code == diag::AlwaysWithoutTimingControl);
}

TEST_CASE("Always with intra-assignment timing controls") {
    {
        // with timing control
        auto& code = R"(
module m;
    logic clk;
    always clk = #1 ~clk;
endmodule
)";

        Compilation compilation;
        AnalysisManager analysisManager;

        auto diags = analyze(code, compilation, analysisManager);
        CHECK_DIAGS_EMPTY;
    }

    {

        // without timing control
        auto& code = R"(
    module m;
        logic clk;
        always clk = ~clk;
        endmodule
    )";
        Compilation compilation;
        AnalysisManager analysisManager;

        auto diags = analyze(code, compilation, analysisManager);
        REQUIRE(diags.size() == 1);
        CHECK(diags[0].code == diag::AlwaysWithoutTimingControl);
    }
}

struct CustomState : public DataFlowState {};

class CustomDFA : public DataFlowAnalysis<CustomDFA, CustomState> {
public:
    std::string& callName;

    CustomDFA(AnalysisContext& context, const Symbol& symbol, std::string& callName) :
        DataFlowAnalysis(context, symbol, false), callName(callName) {}

    void handle(const CallExpression& call) {
        DataFlowAnalysis::handle(call);
        callName = std::string(call.getSubroutineName());
    }
};

TEST_CASE("Custom DFA API test") {
    auto& code = R"(
function void foo;
endfunction

module m;
    always_comb foo();
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    std::string callName;

    analysisManager.setCustomDFAProvider([&](AnalysisContext& context, const Symbol& symbol,
                                             const AnalyzedProcedure* parentProcedure) {
        CustomDFA dfa(context, symbol, callName);
        dfa.run();

        if (dfa.bad)
            return AnalyzedProcedure(symbol, parentProcedure);
        else
            return AnalyzedProcedure(context, symbol, parentProcedure, dfa);
    });

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;

    CHECK(callName == "foo");
}

TEST_CASE("always_comb task call with delay") {
    auto& code = R"(
module m;
    task t;
        #5;
    endtask

    always_comb begin
        t();
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BlockingDelayInTask);
}
