// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

static void ltrim(std::string& s) {
    s.erase(s.begin(),
            std::find_if(s.begin(), s.end(), [](unsigned char ch) { return !std::isspace(ch); }));
}

static std::string testInferredClock(const char* text) {
    Compilation compilation;
    AnalysisManager analysisManager;

    auto fullText = fmt::format(R"(
module m(input clk_default);
    default clocking @clk_default; endclocking
    property p;
        1;
    endproperty
{}
endmodule)",
                                text);

    auto [diags, design] = analyze(fullText, compilation, analysisManager);
    if (!diags.empty()) {
        FAIL_CHECK(report(diags));
        return "";
    }

    REQUIRE(design.topInstances.size() == 1);
    auto& instance = design.topInstances[0];
    auto body = instance.tryGet();
    REQUIRE(body);
    REQUIRE(body->procedures.size() == 1);
    auto& proc = body->procedures[0];
    auto inferredClock = proc.getInferredClock();
    if (!inferredClock)
        return "";

    REQUIRE(inferredClock->syntax);
    auto result = inferredClock->syntax->toString();
    ltrim(result);
    return result;
}

TEST_CASE("Procedure inferred clocks") {
    CHECK(testInferredClock(R"(
        logic clk;
        always @(posedge clk) begin assert property(p); end
    )") == "@(posedge clk)");

    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always_ff @(posedge clk iff reset == 0 or posedge reset) begin
            cnt <= reset ? 0 : cnt + 1;
            assert property (p);
        end
    )") == "posedge clk iff reset == 0");

    // Reset is used in the procedure, clk doesn't match the edge pattern.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always_ff @(clk iff reset == 0 or posedge reset) begin
            cnt <= #5 reset ? 0 : cnt + 1;
            assert property (p);
        end
    )") == "clk_default");

    // No inferred clock in final blocks.
    CHECK(testInferredClock(R"(
        final begin
            assert property (p);
        end
    )") == "clk_default");

    // Blocking assignment with intra-assignment delay.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always @(posedge clk iff reset == 0 or posedge reset) begin
            cnt = #5 reset ? 0 : cnt + 1;
            assert property (p);
        end
    )") == "clk_default");

    // Multiple event controls.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always @(posedge clk iff reset == 0 or posedge reset) begin
            @(posedge clk) begin end
            assert property (p);
        end
    )") == "clk_default");

    // Delay control.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always @(posedge clk iff reset == 0 or posedge reset) begin
            #5 begin end
            assert property (p);
        end
    )") == "clk_default");

    // Wait control.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always @(posedge clk iff reset == 0 or posedge reset) begin
            wait (cnt) begin end
            assert property (p);
        end
    )") == "clk_default");

    // Multiple matching edge expressions.
    CHECK(testInferredClock(R"(
        logic clk, reset;
        logic [7:0] cnt;
        always @(posedge clk iff reset == 0 or negedge clk) begin
            assert property (p);
        end
    )") == "clk_default");

    // Single matching event variable.
    CHECK(testInferredClock(R"(
        event ev1, ev2;
        always @(ev1 or ev2) begin
            ->ev2;
            assert property (p);
        end
    )") == "ev1");

    // Multiple matching event variables.
    CHECK(testInferredClock(R"(
        event ev1, ev2;
        always @(ev1 or ev2) begin
            assert property (p);
        end
    )") == "clk_default");

    // Single matching clocking block.
    CHECK(testInferredClock(R"(
        logic clk;
        clocking cb @(posedge clk);
        endclocking

        always @(cb) begin
            assert property (p);
        end
    )") == "@(cb)");

    // Multiple matching clocking blocks.
    CHECK(testInferredClock(R"(
        logic clk;
        clocking cb @(posedge clk);
        endclocking

        always @(cb or cb) begin
            assert property (p);
        end
    )") == "clk_default");
}

TEST_CASE("Assertions missing clocks") {
    auto& text = R"(
module m(input d, clock, mclk, reset, d1, output logic [3:0] cnt, logic q1);
    logic q;
    property r3;
        q != d;
    endproperty

    always_ff @(clock iff reset == 0 or posedge reset) begin
        cnt <= reset ? 0 : cnt + 1;
        q <= $past(d1); // no inferred clock
        r3_p: assert property (r3); // no inferred clock
    end

    property r4;
        q != d;
    endproperty

    always @(posedge mclk) begin
        #10 q1 <= d1; // delay prevents clock inference
        @(negedge mclk) // event control prevents clock inference
        #10 q1 <= !d1;
        r4_p: assert property (r4); // no inferred clock
    end
endmodule

module examples_with_default (input logic a, b, c, clk);
    property q1;
        $rose(a) |-> ##[1:5] b;
    endproperty

    property q2;
        @(posedge clk) q1;
    endproperty

    default clocking posedge_clk @(posedge clk);
        property q3;
            $fell(c) |=> q1; // legal: q1 has no clocking event
        endproperty

        property q4;
            $fell(c) |=> q2;
                // legal: q2 has clocking event identical to that of
                // the clocking block
        endproperty

        // sequence s1;
        //     @(posedge clk) b[*3];
        //         // illegal: explicit clocking event in clocking block
        // endsequence
    endclocking

    property q5;
        @(negedge clk) b[*3] |=> !b;
    endproperty

    always @(negedge clk)
    begin
        a1: assert property ($fell(c) |=> q1);
            // legal: contextually inferred leading clocking event,
            // @(negedge clk)
        a2: assert property (posedge_clk.q4);
            // legal: will be queued (pending) on negedge clk, then
            // (if matured) checked at next posedge clk (see 16.14.6)
        a3: assert property ($fell(c) |=> q2);
            // illegal: multiclocked property with contextually
            // inferred leading clocking event
        a4: assert property (q5);
            // legal: contextually inferred leading clocking event,
            // @(negedge clk)
    end

    property q6;
        q1 and q5;
    endproperty

    a5: assert property (q6);
        // illegal: default leading clocking event, @(posedge clk),
        // but semantic leading clock is not unique
    a6: assert property ($fell(c) |=> q6);
        // legal: default leading clocking event, @(posedge clk),
        // is the unique semantic leading clock

    sequence s2;
        $rose(a) ##[1:5] b;
    endsequence

    c1: cover property (s2);
        // legal: default leading clocking event, @(posedge clk)
    c2: cover property (@(negedge clk) s2);
        // legal: explicit leading clocking event, @(negedge clk)
    c3: cover property (@(negedge clk) disable iff (c) s2);
        // legal: explicit leading clocking event, @(negedge clk)
endmodule

module examples_without_default (input logic a, b, c, clk);
    property q1;
        $rose(a) |-> ##[1:5] b;
    endproperty

    property q5;
        @(negedge clk) b[*3] |=> !b;
    endproperty

    property q6;
        q1 and q5;
    endproperty

    a5: assert property (q6);
        // illegal: no leading clocking event
    a6: assert property ($fell(c) |=> q6);
        // illegal: no leading clocking event

    sequence s2;
        $rose(a) ##[1:5] b;
    endsequence

    c1: cover property (s2);
        // illegal: no leading clocking event
    c2: cover property (@(negedge clk) s2);
        // legal: explicit leading clocking event, @(negedge clk)

    sequence s3;
        @(negedge clk) s2;
    endsequence

    c3: cover property (s3);
        // legal: leading clocking event, @(negedge clk),
        // determined from declaration of s3
    c4: cover property (s3 ##1 b);
        // illegal: no default, inferred, or explicit leading
        // clocking event and maximal property is not an instance
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::AssertionNoClock);
    CHECK(diags[3].code == diag::AssertionNoClock);
    CHECK(diags[4].code == diag::AssertionNoClock);
    CHECK(diags[5].code == diag::AssertionNoClock);
}

TEST_CASE("Assertions clock resolution rules with clocking blocks") {
    auto& text = R"(
module m(input a, b, clk, clk2, clk3);
    clocking primary_clk @(posedge clk);
        property p3; not (a ##2 b); endproperty
    endclocking

    assert property (primary_clk.p3);

    property p2;
        @(posedge clk2) a and @(posedge clk3) b;
    endproperty

    clocking cb1 @(posedge clk);
        property p1; not p2; endproperty
    endclocking

    assert property (cb1.p1);

    clocking cb2 @(posedge clk2);
        property p1; not primary_clk.p3; endproperty
    endclocking

    assert property (cb2.p1);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MulticlockedInClockingBlock);
    CHECK(diags[1].code == diag::DifferentClockInClockingBlock);
}

TEST_CASE("Multiclocked sequences with invalid concat / binary ops") {
    auto& text = R"(
module m(input d, clk1, clk2, clk3);
    sequence s1;
        @(posedge clk2 or clk3) d;
    endsequence

    property p1;
        s1 ##2 @(posedge clk2) d;
    endproperty

    sequence s2;
        s1 intersect @(posedge clk1 or clk2 or clk3) d;
    endsequence

    assert property (p1);
    assert property (s2);
    assert property (@(posedge clk1) d and @(posedge clk2) d);
    assert property (first_match(@(posedge clk1) d and @(posedge clk2) d));
endmodule

module multiclock();
   reg clk, clk1, clk2, clk3;
   reg b0, b1, b2, b3, b4;

   sequence a1;
      (@(posedge clk) b1) and (@(posedge clk) b2) and (@(posedge clk1) b3);  // illegal
   endsequence // a1

   assert property(a1);

   sequence a2;
      (@(posedge clk) b1[*0:1]) ##1 (@(posedge clk1) b2);  // illegal - empty match of b1
   endsequence // a2

   assert property(a2);

   sequence a3;
      (@(posedge clk) b1[*0:1]) ##1 (@(posedge clk) b2);  // legal - empty match of b1 but it's same clocked
   endsequence //a3

   assert property(a3);

   sequence a4;
      (b1[*0:1]) ##1 (b2);  // legal - empty match of b1 but it's unclocked
   endsequence // a4

   assert property(@(posedge clk) a4);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[1].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[2].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[3].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[4].code == diag::MulticlockedSeqEmptyMatch);
}
