// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

TEST_CASE("Tautological out-of-range comparisons") {
    auto& code = R"(
module m;
    logic [3:0] a, b;
    byte sb;
    logic [7:0] x;
    logic c;
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
    state_t s;

    always_comb begin
        c = a == 20;
        c = 16 > a;
        c = sb < 200;
        c = a > -1;
        c = (x & 8'h0F) < 16;
        c = a + b < 32;
        c = s != 5;
        c = (a < b) == 2;
        c = {4'b0, a} < 16;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:11:15: warning: comparison of 4-bit unsigned value == 20 is always false [-Wtautological-range-compare]
        c = a == 20;
            ~ ^~ ~~
source:12:16: warning: comparison of 4-bit unsigned value < 16 is always true [-Wtautological-range-compare]
        c = 16 > a;
            ~~ ^ ~
source:13:16: warning: comparison of 8-bit signed value < 200 is always true [-Wtautological-range-compare]
        c = sb < 200;
            ~~ ^ ~~~
source:14:15: warning: comparison of 4-bit unsigned value > 4294967295 is always false [-Wtautological-range-compare]
        c = a > -1;
            ~ ^ ~~
source:15:25: warning: comparison of 4-bit unsigned value < 16 is always true [-Wtautological-range-compare]
        c = (x & 8'h0F) < 16;
             ~~~~~~~~~  ^ ~~
source:16:19: warning: comparison of 5-bit unsigned value < 32 is always true [-Wtautological-range-compare]
        c = a + b < 32;
            ~~~~~ ^ ~~
source:17:15: warning: comparison of 2-bit unsigned value != 5 is always true [-Wtautological-range-compare]
        c = s != 5;
            ~ ^~ ~
source:18:21: warning: comparison of 1-bit unsigned value == 2 is always false [-Wtautological-range-compare]
        c = (a < b) == 2;
             ~~~~~  ^~ ~
source:19:23: warning: comparison of 4-bit unsigned value < 16 is always true [-Wtautological-range-compare]
        c = {4'b0, a} < 16;
            ~~~~~~~~~ ^ ~~
)");
}

TEST_CASE("Tautological comparison value ranges") {
    auto& code = R"(
module m;
    logic [3:0] a, b;
    logic [7:0] x;
    logic signed [3:0] sa;
    byte sb;
    int i;
    logic c;

    always_comb begin
        // None of these are tautological.
        c = a + b < 16;
        c = a + b < 31;
        c = a - b < 16;
        c = a * b < 225;
        c = x % 10 == 10;
        c = (x << 4) > 15;
        c = (x >> i) > 15;
        c = -a == 1;
        c = ~a == 32'hFFFFFFF0;
        c = sa == 4'hF;
        c = sb == 8'hFF;
        c = x[3:0] == a;
        c = i < 200;
        c = a > 0;
        c = (a | b) < 15;
        c = $signed(a) < 7;

        // These are.
        c = a * b < 256;
        c = (x >> 4) < 16;
        c = (x % 10) < 256;
        c = (x & a) > 15;
        c = sa < 8;
        c = sa == 5'h1F;
        c = $unsigned(sa) < 16;
        c = (x / 2) < 256;
        c = (a + 0) < 16;
        c = (0 + a) < 16;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::OutOfRangeCompare);
    CHECK(diags[1].code == diag::OutOfRangeCompare);
    CHECK(diags[2].code == diag::OutOfRangeCompare);
    CHECK(diags[3].code == diag::LimitCompare);
    CHECK(diags[4].code == diag::OutOfRangeCompare);
    CHECK(diags[5].code == diag::OutOfRangeCompare);
    CHECK(diags[6].code == diag::OutOfRangeCompare);
    CHECK(diags[7].code == diag::OutOfRangeCompare);
    CHECK(diags[8].code == diag::OutOfRangeCompare);
    CHECK(diags[9].code == diag::OutOfRangeCompare);
}

TEST_CASE("Tautological limit comparisons") {
    auto& code = R"(
`define LIMIT 15
module m;
    logic [3:0] a;
    logic c;

    always_comb begin
        c = a >= 0;
        c = a < 0;
        c = a <= 15;
        c = a > 15;
        c = a > `LIMIT;
        c = a >= 1;
    end

    initial begin
        for (logic [3:0] i = 15; i >= 0; i--) begin end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:8:15: warning: comparison of 4-bit unsigned value >= 0 is always true [-Wtautological-limit-compare]
        c = a >= 0;
            ~ ^~ ~
source:9:15: warning: comparison of 4-bit unsigned value < 0 is always false [-Wtautological-limit-compare]
        c = a < 0;
            ~ ^ ~
source:10:15: warning: comparison of 4-bit unsigned value <= 15 is always true [-Wtautological-limit-compare]
        c = a <= 15;
            ~ ^~ ~~
source:11:15: warning: comparison of 4-bit unsigned value > 15 is always false [-Wtautological-limit-compare]
        c = a > 15;
            ~ ^ ~~
source:17:36: warning: comparison of 4-bit unsigned value >= 0 is always true [-Wtautological-limit-compare]
        for (logic [3:0] i = 15; i >= 0; i--) begin end
                                 ~ ^~ ~
)");
}

TEST_CASE("Tautological comparisons not reported for parameters and macros") {
    auto& code = R"(
`define IN_RANGE(x) ((x) >= 0 && (x) < 16)
module m #(parameter int DEPTH = 16, parameter int W = 4);
    logic [W-1:0] addr;
    logic [3:0] a;
    logic c;
    localparam int MAX = 15;

    always_comb begin
        c = addr < DEPTH;
        c = a <= MAX;
        c = DEPTH > 8;
        c = `IN_RANGE(a);
        c = a === 4'bx;
    end

    for (genvar g = 0; g < 4; g++) begin : gen
        logic d;
        always_comb d = g < 8;
    end

    logic e;
    initial begin
        for (int k = 0; k < 4; k++) begin
            e = k < 100;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Tautological comparisons in unrolled loops reported once") {
    auto& code = R"(
module m;
    logic [3:0] a;
    logic e;
    initial begin
        for (int k = 0; k < 4; k++) begin
            e = a == 20;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::OutOfRangeCompare);
}

TEST_CASE("Tautological comparisons of unrolled loop variables") {
    // The loop variable has a known value on each unrolled iteration,
    // but that shouldn't hide comparisons that are tautological regardless.
    auto& code = R"(
module m;
    logic c;
    initial begin
        for (logic [2:0] k = 0; k < 4; k++) begin
            c = k == 9;
            c = k != k;
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::OutOfRangeCompare);
    CHECK(diags[1].code == diag::SelfCompare);
}

TEST_CASE("Tautological comparisons in non-procedural code") {
    auto& code = R"(
module m;
    logic [3:0] a;
    logic [7:0] x;
    wire w = a > 20;
    logic l = (x & 8'h0F) == 8'h1F;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::OutOfRangeCompare);
    CHECK(diags[1].code == diag::BitwiseCompare);
}

TEST_CASE("Tautological comparisons in unreachable code") {
    auto& code = R"(
module m;
    logic [3:0] a;
    logic c;
    localparam bit P = 0;
    always_comb begin
        if (P)
            c = a == 20;
        else
            c = 0;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Tautological self comparisons") {
    auto& code = R"(
module m;
    logic [3:0] a;
    bit [3:0] b;
    int i;
    int arr[4];
    real r;
    logic c;

    always_comb begin
        c = i == i;
        c = a != a;
        c = a < a;
        c = a === a;
        c = a !=? a;
        c = b >= b;
        c = arr[i] == arr[i];

        // None of these warn.
        c = a == a;
        c = a <= a;
        c = r == r;
        c = $random == $random;
        c = arr[i] == arr[i + 1];
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:11:15: warning: self-comparison always evaluates to true [-Wtautological-self-compare]
        c = i == i;
            ~ ^~ ~
source:12:15: warning: self-comparison always evaluates to false [-Wtautological-self-compare]
        c = a != a;
            ~ ^~ ~
source:13:15: warning: self-comparison always evaluates to false [-Wtautological-self-compare]
        c = a < a;
            ~ ^ ~
source:14:15: warning: self-comparison always evaluates to true [-Wtautological-self-compare]
        c = a === a;
            ~ ^~~ ~
source:15:15: warning: self-comparison always evaluates to false [-Wtautological-self-compare]
        c = a !=? a;
            ~ ^~~ ~
source:16:15: warning: self-comparison always evaluates to true [-Wtautological-self-compare]
        c = b >= b;
            ~ ^~ ~
source:17:20: warning: self-comparison always evaluates to true [-Wtautological-self-compare]
        c = arr[i] == arr[i];
            ~~~~~~ ^~ ~~~~~~
)");
}

TEST_CASE("Tautological bitwise comparisons") {
    auto& code = R"(
module m;
    logic [7:0] x;
    logic [3:0] a;
    logic c;

    always_comb begin
        c = (x & 8'h4) == 8'h8;
        c = (x | 8'h4) != 8'h1;
        c = 8'h8 === (8'h4 & x);
        c = (a & 3) == 7;

        // None of these warn.
        c = (x & 8'h4) == 8'h4;
        c = (x | 8'h4) == 8'h5;
        c = (x & 8'h4) < 8'h4;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:8:24: warning: bitwise comparison always evaluates to false [-Wtautological-bitwise-compare]
        c = (x & 8'h4) == 8'h8;
             ~~~~~~~~  ^~ ~~~~
source:9:24: warning: bitwise comparison always evaluates to true [-Wtautological-bitwise-compare]
        c = (x | 8'h4) != 8'h1;
             ~~~~~~~~  ^~ ~~~~
source:10:18: warning: bitwise comparison always evaluates to false [-Wtautological-bitwise-compare]
        c = 8'h8 === (8'h4 & x);
            ~~~~ ^~~  ~~~~~~~~
source:11:21: warning: bitwise comparison always evaluates to false [-Wtautological-bitwise-compare]
        c = (a & 3) == 7;
             ~~~~~  ^~ ~
)");
}

TEST_CASE("Tautological overlapping comparisons") {
    auto& code = R"(
module m;
    int i;
    logic [3:0] a;
    logic c;

    always_comb begin
        c = i < 5 && i > 10;
        c = i != 1 || i != 2;
        c = i == 1 && i == 2;
        c = i > 5 || i < 10;
        c = (i < 5) & (i > 10);
        c = i == 1 || i != 1;
        c = 5 > i && 10 < i;
        c = a <= 3 && a >= 12;

        // None of these warn.
        c = i >= 5 && i <= 10;
        c = i < 5 || i > 10;
        c = i < 5 && a > 10;
        c = i == 1 || i == 2;
        c = i != 1 && i != 2;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:8:19: warning: non-overlapping comparisons always evaluate to false [-Wtautological-overlap-compare]
        c = i < 5 && i > 10;
            ~~~~~ ^~ ~~~~~~
source:9:20: warning: overlapping comparisons always evaluate to true [-Wtautological-overlap-compare]
        c = i != 1 || i != 2;
            ~~~~~~ ^~ ~~~~~~
source:10:20: warning: non-overlapping comparisons always evaluate to false [-Wtautological-overlap-compare]
        c = i == 1 && i == 2;
            ~~~~~~ ^~ ~~~~~~
source:11:19: warning: overlapping comparisons always evaluate to true [-Wtautological-overlap-compare]
        c = i > 5 || i < 10;
            ~~~~~ ^~ ~~~~~~
source:12:21: warning: non-overlapping comparisons always evaluate to false [-Wtautological-overlap-compare]
        c = (i < 5) & (i > 10);
             ~~~~~  ^  ~~~~~~
source:13:20: warning: overlapping comparisons always evaluate to true [-Wtautological-overlap-compare]
        c = i == 1 || i != 1;
            ~~~~~~ ^~ ~~~~~~
source:14:19: warning: non-overlapping comparisons always evaluate to false [-Wtautological-overlap-compare]
        c = 5 > i && 10 < i;
            ~~~~~ ^~ ~~~~~~
source:15:20: warning: non-overlapping comparisons always evaluate to false [-Wtautological-overlap-compare]
        c = a <= 3 && a >= 12;
            ~~~~~~ ^~ ~~~~~~~
)");
}

TEST_CASE("Tautological negation comparisons") {
    auto& code = R"(
module m;
    logic a, b, c;

    always_comb begin
        c = a || !a;
        c = !a && a;

        // None of these warn.
        c = a || !b;
        c = $random || !$random;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:6:15: warning: '||' of a value and its negation always evaluates to true [-Wtautological-negation-compare]
        c = a || !a;
            ~ ^~ ~~
source:7:16: warning: '&&' of a value and its negation always evaluates to false [-Wtautological-negation-compare]
        c = !a && a;
            ~~ ^~ ~
)");
}

TEST_CASE("Tautological comparisons with less common expression kinds") {
    auto& code = R"(
function automatic int f;
    return 1;
endfunction

module m;
    logic [3:0] a;
    int i, j;
    typedef int pair_t[2];
    logic c;

    always_comb begin
        c = (a inside {1, 2}) != (a inside {1, 2});
        c = pair_t'{i, j} != pair_t'{i, j};
        c = a == {8{1'b1}};
        c = a == (1 ? 5'd16 : 5'd0);

        // None of these warn.
        c = f() == f();
        c = (i++) == (i++);
        c = (a inside {1, 2}) != (a inside {1, 3});
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::SelfCompare);
    CHECK(diags[1].code == diag::SelfCompare);
    CHECK(diags[2].code == diag::OutOfRangeCompare);
    CHECK(diags[3].code == diag::OutOfRangeCompare);

    // The increments get a different warning, but not a self-comparison one.
    CHECK(diags[4].code == diag::MultiWriteExpr);
}

TEST_CASE("Tautological comparisons of selects") {
    auto& code = R"(
module m;
    logic [7:0] x;
    logic signed [7:0] sx;
    byte arr[4];
    logic [3:0][7:0] pk;
    struct packed { logic [2:0] f; logic [4:0] g; } s;
    int i;
    logic c;

    always_comb begin
        c = x[3:0] < 16;
        c = x[i] == 2;
        c = arr[i] < 200;
        c = pk[1] < 256;
        c = s.f == 8;

        // None of these warn.
        c = sx[3:0] == 15;
        c = x[i+:2] < 3;
        c = arr[i] < 127;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:12:20: warning: comparison of 4-bit unsigned value < 16 is always true [-Wtautological-range-compare]
        c = x[3:0] < 16;
            ~~~~~~ ^ ~~
source:13:18: warning: comparison of 1-bit unsigned value == 2 is always false [-Wtautological-range-compare]
        c = x[i] == 2;
            ~~~~ ^~ ~
source:14:20: warning: comparison of 8-bit signed value < 200 is always true [-Wtautological-range-compare]
        c = arr[i] < 200;
            ~~~~~~ ^ ~~~
source:15:19: warning: comparison of 8-bit unsigned value < 256 is always true [-Wtautological-range-compare]
        c = pk[1] < 256;
            ~~~~~ ^ ~~~
source:16:17: warning: comparison of 3-bit unsigned value == 8 is always false [-Wtautological-range-compare]
        c = s.f == 8;
            ~~~ ^~ ~
)");
}

TEST_CASE("Tautological comparisons of system function results") {
    auto& code = R"(
class C;
    rand int x;
endclass

module m;
    int arr[string];
    string k;
    logic [7:0] x;
    int i;
    C obj;
    logic c;

    always_comb begin
        c = $test$plusargs("foo") == 2;
        c = arr.exists("a") > 1;
        c = arr.first(k) < 2;
        c = obj.randomize() == 5;
        c = $unsigned(x[3:0]) < 16;

        // None of these warn.
        c = arr.first(k) == -1;
        c = $test$plusargs("foo") == 1;
        c = $countones(x) < 8;
        c = $signed(x[3:0]) < 7;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:15:35: warning: comparison of 2-bit signed value == 2 is always false [-Wtautological-range-compare]
        c = $test$plusargs("foo") == 2;
            ~~~~~~~~~~~~~~~~~~~~~ ^~ ~
source:16:29: warning: comparison of 2-bit signed value > 1 is always false [-Wtautological-limit-compare]
        c = arr.exists("a") > 1;
            ~~~~~~~~~~~~~~~ ^ ~
source:17:26: warning: comparison of 2-bit signed value < 2 is always true [-Wtautological-range-compare]
        c = arr.first(k) < 2;
            ~~~~~~~~~~~~ ^ ~
source:18:29: warning: comparison of 2-bit signed value == 5 is always false [-Wtautological-range-compare]
        c = obj.randomize() == 5;
            ~~~~~~~~~~~~~   ^~ ~
source:19:31: warning: comparison of 4-bit unsigned value < 16 is always true [-Wtautological-range-compare]
        c = $unsigned(x[3:0]) < 16;
            ~~~~~~~~~~~~~~~~~ ^ ~~
)");
}
