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
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::NoUniqueClock);
    CHECK(diags[3].code == diag::AssertionNoClock);
    CHECK(diags[4].code == diag::AssertionNoClock);
    CHECK(diags[5].code == diag::AssertionNoClock);
    CHECK(diags[6].code == diag::AssertionNoClock);
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
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[1].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[2].code == diag::NoUniqueClock);
    CHECK(diags[3].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[4].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[5].code == diag::MulticlockedSeqEmptyMatch);
}

TEST_CASE("Assertion unique clock -- LRM invalid example") {
    // This example comes from the LRM but I believe the "illegal"
    // comment is incorrect. Nothing in the wording makes this illegal.
    // No other tools error on this either.
    auto& text = R"(
module m (input logic a, b, c, clk);
    property q1;
        $rose(a) |-> ##[1:5] b;
    endproperty

    property q2;
        @(posedge clk) q1;
    endproperty

    always @(negedge clk)
    begin
        a3: assert property ($fell(c) |=> q2);
            // illegal: multiclocked property with contextually
            // inferred leading clocking event
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Clock resolution tests 3") {
    auto& text = R"(
module m9(input wire clk, input bit a, input int b, c);
    covergroup p_cg with function sample(bit a, int x);
        coverpoint x;
        cross x, a;
    endgroup : p_cg

    p_cg cg1 = new;

    property p1;
        int x;
        @(posedge clk)(a, x = b) ##1 (c, cg1.sample(a, x));
    endproperty : p1

    c1: cover property (p1);  // legal
endmodule

module c2(input logic a, b, c, clk, clk_n, req1, req2, rst_n);
   sequence seqX;
      @(negedge clk) a ##1 @(posedge clk_n)b;
   endsequence // seqX

   assert property (seqX); // legal
endmodule // c2

module c3(input logic a, b, c, clk, clk_n, req1, req2, rst_n);
   sequence seqX;
      @(negedge clk) a ##1 @(posedge clk_n)b;
   endsequence // seqX

   default clocking posedge_clk @(posedge clk);
   endclocking // posedge_clk

   assert property (seqX); // legal
endmodule // c2

module c4(input logic a, b, c, clk, clk_n, req1, req2, rst_n);
   sequence seqX;
      @(negedge clk) a ##1 @(posedge clk_n)b;
   endsequence // seqX

   // This was illegal in LRM 1800-2005 but was made legal in 1800-2009
   always @(posedge clk) begin
      assert property (seqX); // Illegal
   end
endmodule // c4
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Clock resolution tests 4") {
    auto& text = R"(
module c5(input logic a, b, c, clk, clk_n, req1, req2, rst_n);
   property q1;
      $rose(a) |-> ##[1:5] b;
   endproperty

   property q2;
      @(posedge clk) q1;
   endproperty // q2

   property q5;
      @(negedge clk) b[*3] |=> !b;
   endproperty

   property q6;
      q1 and q5;
   endproperty

   a5: assert property (q6); // Illegal
        // illegal: no leading clocking event
   a6: assert property ($fell(c) |=> q6); // Illegal
        // illegal: no leading clocking event

   sequence s2;
      $rose(a) ##[1:5] b;
   endsequence

   c1: assert property (s2); // Illegal
        // illegal: no leading clocking event
   c2: assert property (@(negedge clk) s2);
        // legal: explicit leading clocking event, @(negedge clk)

   sequence s3;
      @(negedge clk) s2;
   endsequence

   c4: assert property (s3 ##1 b); // Illegal
   // illegal: no default, inferred, or explicit leading
   // clocking event and maximal property is not an instance

   sequence seqA;
      req1 ##3 req2;
   endsequence

   property prop;
      @(posedge clk) seqA;
   endproperty

   assert property (prop);

   sequence seqB;
      @(posedge clk) req1 ##3 req2;
   endsequence

   property propB;
      seqB;
   endproperty

   assert property (propB);

   sequence seqC;
      seqB ##3 req2;
   endsequence

   property propC;
      seqC;
   endproperty

   assert property (propC);
   assert property (seqB ##2 req2); // Illegal
   assert property (req2 ##3 seqB); // Illegal
   assert property (seqB);
   assert property (seqB ## 1 seqB); // Illegal
   assert property (seqB ## 1 seqB ##2 a); // Illegal
   assert property (prop or propC); // Illegal
   assert property (prop or prop);
   assert property (@(negedge clk) a ##1 @(posedge clk)b);

   sequence seqX;
      @(negedge clk) a ##1 @(posedge clk_n)b;
   endsequence

   always @(posedge clk, posedge rst_n, negedge clk_n)
     if (rst_n) begin
	    assert property (propC);
     end
     else if (~clk_n) begin
        assert property (seqB ##2 req2);
     end
     else begin
        assert property (req2 ##3 seqB);
        assert property (seqB);
        assert property (seqB ## 1 seqB);
        assert property (seqB ## 1 seqB ##2 a);
        assert property (prop or propC);
        assert property (prop or prop);
        assert property (@(negedge clk) a);
        assert property ($fell(c) |=> q2);
        assert property (seqX);
     end
endmodule // c5
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::AssertionNoClock);
    CHECK(diags[3].code == diag::AssertionNoClock);
    CHECK(diags[4].code == diag::AssertionNoClock);
    CHECK(diags[5].code == diag::AssertionNoClock);
    CHECK(diags[6].code == diag::AssertionNoClock);
    CHECK(diags[7].code == diag::AssertionNoClock);
    CHECK(diags[8].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 5") {
    auto& text = R"(
module c6(input logic clk, clk1, clk2, a, b, c, d, e, f);
   property p;
   logic v = e;
   (@(posedge clk1) (a == v)[*1:$] |-> b)
   and
   (@(posedge clk2) c[*1:$] |-> d == v)
   ;
   endproperty
a1: assert property (@(posedge clk) f |=> p);
endmodule // c6

module c7(input logic mclk, scanclk, d, d1);
   reg q;
   property r1;
      q != d;
   endproperty

   always @(posedge mclk) begin
      q <= d1;
      r1_p1: assert property (r1);
      r1_p2: assert property (@(posedge scanclk)r1);
   end
endmodule // c7

module c8(input logic clock, reset, d, d1);
   int cnt;
   reg q;
   property r2;
      q != d;
   endproperty

   always_ff @(posedge clock iff reset == 0 or posedge reset) begin
      cnt <= reset ? 0 : cnt + 1;
      q <= $past(d1);
      r2_p: assert property (r2);
   end
endmodule // c8

module c9(input logic clock, reset, d, d1);
   int cnt;
   reg q;
   property r3;
      q != d;
   endproperty

   always_ff @(clock iff reset == 0 or posedge reset) begin
      cnt <= reset ? 0 : cnt + 1;
      q <= $past(d1); // no inferred clock
      r3_p: assert property (r3); // no inferred clock
   end
endmodule // c9

module c10(logic a, b, c, d, rst1, clk1, clk2);
    logic rst;
    default clocking @(negedge clk1); endclocking
    default disable iff rst1;
    property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                        rst = $inferred_disable);
        @clk disable iff (rst)
            (start_event ##0 end_event[->1]) |=> form;
    endproperty

    a1: assert property (p_triggers(a, b, c));
    a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

    always @(posedge clk2 or posedge rst) begin
        if (rst) begin end
        else begin
            a3: assert property (p_triggers(a, b, c));
        end
    end
endmodule // c10
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 6") {
    auto& text = R"(
module c11(logic a, b, c, d, rst1, clk1, clk2);
   logic rst;
   default clocking @(negedge clk1); endclocking
   default disable iff rst1;

   property p_triggers(start_event, end_event, form, clk = $inferred_clock,
		       rst = $inferred_disable);
      @clk disable iff (rst)
	(start_event ##0 end_event[->1]) |=> form;
   endproperty

   property p_multiclock(clkw, clkx = $inferred_clock, clky, w, x, y, z);
      @clkw w ##1 @clkx x |=> @clky y ##1 z;
   endproperty

   a1: assert property (p_triggers(a, b, c));
   a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

   always @(posedge clk2 or posedge rst) begin
      if (!rst)
      begin
	 a3: assert property (p_triggers(a, b, c));
      end
   end
   a4: assert property(p_multiclock(negedge clk2, , posedge clk1,
				    a, b, c, d) );
endmodule // c11

module c12(input logic clock, reset, d, d1);
   int cnt;
   reg q;
   property r2;
      @(posedge clock)q != d;
   endproperty

   always_ff @(posedge clock iff reset == 0 or posedge reset) begin
      cnt <= reset ? 0 : cnt + 1;
      q <= $past(d1);
      r2_p: assert property (r2);
   end
endmodule // c12

module m(input clk, frame1, irdy1);
   logic trdy[5];
   logic data[10];
   int 	 m1_t1_r;
   logic m1_t1_r_flag;
    property p_m1t1r;
    // master1 reading from target 1
        @(posedge clk)
        $fell (frame1 && irdy1) |-> ##3 ($fell (trdy[1])) ## 3 !data[8];
    endproperty

c_m1t1r: cover property(p_m1t1r)
  begin
     m1_t1_r++;
     if (m1_t1_r == 3) m1_t1_r_flag = 1'b1;
  end
endmodule // m
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Clock resolution tests 7") {
    auto& text = R"(
module m2(input clk, enable1, input int a, aa);
   property p_local_var1;
      int lvar1;
      @(posedge clk)
	($rose(enable1), lvar1 = a) |-> ##4 (aa == (lvar1 * lvar1 * lvar1));
   endproperty // p_local_var1

   a_local_var1: assert property(p_local_var1);
endmodule // m2

module m3(input clk1, clk2, a, b);
   sequence s_a;
      @(posedge clk1) $rose(a);
   endsequence // s_a

   sequence s_b;
      @(posedge clk2) $rose(b);
   endsequence // s_b

   property p_match;
      @(posedge clk2) s_a.matched |=> s_b;
   endproperty // p_match

   a_match: assert property(p_match);
endmodule // m3

module m4(input clk);
   reg a;
   default clocking def_clk @(posedge clk);
   endclocking

   property i_l;
      1;
   endproperty

   a_i_l: assert property(i_l);

   property s_l;
      "str";
   endproperty

   property v_l;
       a;
   endproperty

   a_v_l: assert property(v_l);
endmodule // m4

module m5(input clk, clk1, a, b);
   property mult_clock_prop;
      @(posedge clk) a and @(posedge clk1) b;
   endproperty // multi_clock_prop

   always @(clk) assert property (mult_clock_prop); // illegal
   initial @(posedge clk) assert property (mult_clock_prop); // illegal
endmodule // m5
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NoUniqueClock);
    CHECK(diags[1].code == diag::NoUniqueClock);
}

TEST_CASE("Clock resolution tests 8") {
    auto& text = R"(
module hint (input
	     clk,
	     clk1,
	     clk2,
	     active,
	     start,
	     request,
	     grant,
	     req,
	     gnt);
sequence d (data,en);
  (!en) ##1 data==0;
endsequence

property p1;
  @(posedge clk) disable iff(!active)
  start |-> request ##2 (grant==1);
endproperty

  assert property (p1); // property can be concatenated with logical operators
// inside property first_match , within and throughout
// checking property for multiclocked signals
  //=================================================
  // Sequence Specification Layer
  //=================================================
  sequence multi_clock_seq;
     @(posedge clk1) req  ##1  @(posedge clk2) gnt;
  endsequence

  //=================================================
  // Property Specification Layer
  //=================================================
  property multi_clock_prop;
    @ (posedge clk1)
        req |-> multi_clock_seq;
  endproperty

  //=================================================
  // Assertion Directive Layer
  //=================================================
  multi_clock_assert : assert property (multi_clock_prop);
endmodule // hint
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Clock resolution tests 9") {
    auto& text = R"(
`line 904 "test.sv" 0
module multiclock();
   reg clk, clk1, clk2, clk3;
   reg b0, b1, b2, b3, b4;
   initial clk = 0; always #50 clk = ~clk;
   initial clk1 = 0; always #51 clk1 = ~clk1;

   sequence a1;
      (@(posedge clk1) b1) ##1 (@(posedge clk) b2);
   endsequence // a1

   sequence a2;
      (@(posedge clk1) b1) and (@(posedge clk) b2);
   endsequence // a2

   assert property(a1);
   assert property(a2);
   assert property ((@(posedge clk1) b1) ##1 (@(posedge clk) b2));
   assert property (@(posedge clk1) b1 ##1 @(posedge clk) b2);
   assert property ((@(posedge clk1) b1) and (@(posedge clk) b2));
   assert property (@(posedge clk) b0 ##1 (1 ##1 (@(posedge clk1) b1) and (@(posedge clk) b2)) |=> b3);
   assert property (@(posedge clk) b0 ##1 ((@(posedge clk1) b1) and (@(posedge clk) b2)) |=> b3);
   assert property (@(posedge clk) b0 ##1 ((@(posedge clk1) b1) and (@(posedge clk) b2)));
   assert property ((@(posedge clk1) b1) or (@(posedge clk) b2));
   assert property (##3 (@(posedge clk1) b1) ##1 (@(posedge clk2) b2) ##2 (@(posedge clk3) b3));
   assert property (((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)) until ((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)));
   assert property ( ((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)) |-> ((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)));
   assert property ( @(posedge clk1) b1 until ((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)));
   assert property ( @(posedge clk1) b1 |-> ((@(posedge clk1) b1) ##1 (@(posedge clk2) b2)));
   assert property ( (@(posedge clk) b1) until (@(posedge clk1) b1));
   assert property (sync_accept_on(1) @(posedge clk) b1);
   assert property (accept_on(1) @(posedge clk) b1);
endmodule // multiclock
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[1].code == diag::NoUniqueClock);
    CHECK(diags[2].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[3].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[4].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[5].code == diag::NoUniqueClock);
    CHECK(diags[6].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[7].code == diag::AssertionNoClock);
    CHECK(diags[8].code == diag::AssertionNoClock);
    CHECK(diags[9].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 10") {
    auto& text = R"(
module mc_01(input clk, clk1, clk2);
   reg a, b, c, d, e, f;
   property mult_p8;
      @(posedge clk) a ##1 b |->
	if (c)
	  (1 |=> @(posedge clk1) d)
	  else
	    e ##1 @(posedge clk2) f ;
   endproperty // mult_p8

   assert property (mult_p8);
endmodule // mc_01

module mc_02;
   string a;
   logic  b;
   int 	  c,d,e;
   default clocking posedge_b @(posedge b);
   endclocking // posedge_b

   assert property (always b and c);
   assert property ((always b) and @(negedge b)c);
endmodule

module mc_03;
   string a;
   logic  b;
   int 	  c,d,e;
   restrict property (@(posedge b) case (b) 1, 2, 3: @(negedge b)1 ##1 b; 4: a and b; default: 1 |-> b; endcase);
   cover property (case (b) 1, 2, 3: @(negedge b)1 ##1 b; 4: a and b; default: 1 |-> b; endcase);
   assume property (if (b) a ##1 c else  @(negedge b) d ##1 e);
endmodule

module mc_04;
   logic clk;
   logic reset;
   logic req;
   logic ack;
   logic grant;

   assert property ( @(posedge clk) disable iff( reset)
                  !req ##1 req[*1:$] ##1 !req
                  |->
                  !ack[*1:$] ##1 ack[*1:$] ##1 !ack );

   assert property ( @(posedge clk) disable iff (reset)
                  $rose(req) |=> ack[*0:$] ##1 grant );
endmodule

module decl_in_clocking_block (input logic a, b, c, clk);
   clocking PCLK @(posedge clk);
      property p3;
	    a |=> p4;
      endproperty
   endclocking

   property p4;
      b until c;
   endproperty

   a19: assert property(PCLK.p3);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::NoUniqueClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 11") {
    auto& text = R"(
`line 1034 "test.sv" 0
module mc_05(input logic a, b, clk1, clk2);
a1: assert property(@(posedge clk1) a |->(@(posedge clk2) a) until (@(posedge clk2) b));
a2: assert property(@(posedge clk1) a |-> @(posedge clk2) a[*] ##1 b);
endmodule

module mc_06;
   bit clk;
   logic a, b;
   let x = $past(a && b);
   let y = $past(a && b, , ,@(posedge clk));

   always_comb begin
      a1: assert #0 (x);
      a2: assert #0 (y);
   end

   a3: assert property(@(posedge clk) a |-> x);
   a4: assert property(@(posedge clk) a |-> y);
endmodule

module mc_07;
   bit clk;
   clocking PCLK @(posedge clk);
   endclocking

   logic a, b;
   let x = $past(a && b);
   let y = $past(a && b, , ,@(posedge clk));

   always_comb begin
      a1: assert #0 (x);
      a2: assert #0 (y);
   end

   a3: assert property(@(posedge clk) a |-> x);
   a4: assert property(@(posedge clk) a |-> y);
endmodule

module m_seqprotocol #(parameter int bothedges = 0,
		       parameter type dataType = logic)
   (input logic start, complete, clk, reset,
    dataType dataIn, dataOut);

   if (bothedges) begin :L
      default clocking dclk @clk; endclocking
   end
   else begin :L
      default clocking dclk @(posedge clk); endclocking
   end

   default disable iff reset;

   property match(x, y);
      x |=> !x until_with y;
   endproperty : match

   var type(dataIn) last_dataIn;
   always @L.dclk
     if ($sampled(start))last_dataIn <= $sampled(dataIn);
   a_initial_no_complete:
     assert property ($fell(reset) |-> !complete until_with start);
      a_seq_data_check: assert property (
					 complete |-> dataOut == last_dataIn);
      a_no_start: assert property (match(start, complete));
      a_no_complete: assert property (match(complete, start));
endmodule : m_seqprotocol

module mc_08 (input logic start2, complete2, clk2, reset2,
    int dataIn2, dataOut2);
   m_seqprotocol #(0, int) seqpot1(start2, complete2, clk2, reset2, dataIn2, dataOut2);
endmodule // m

module mc_09 (input logic start2, complete2, clk2, reset2,
    int dataIn2, dataOut2);
   m_seqprotocol #(1, int) seqpot2(start2, complete2, clk2, reset2, dataIn2, dataOut2);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Clock resolution tests 12") {
    auto& text = R"(
module m_s #(parameter int bothedges = 0)
   (input logic  clk);
   if (bothedges) begin :L
     clocking dclk @clk; endclocking
   end
   else begin :L
     clocking dclk @(posedge clk); endclocking
   end

   default clocking dclk @(posedge clk); endclocking

   reg x;
   assert property (x);
endmodule : m_s

module mc_10 (input clk1);
   m_s #(0) seqpot1(clk1);
endmodule // m

module m_s_11 #(parameter int bothedges = 0)
   (input logic  clk);
   if (bothedges) begin :L
     clocking dclk @clk; endclocking
   end
   else begin :L
     default clocking dclk @(posedge clk); endclocking
   end

   reg x;
   assert property (x);
endmodule : m_s_11

module mc_11 (input clk1);
   m_s_11 #(0) seqpot1(clk1);
endmodule // m

module mc_12 (input logic clk2);
   m_s_11 #(1) seqpot2(clk2);
endmodule

module mc_14;
    // Define clock signals
   logic clk1, clk2;
   logic  x, y;

    // Define sequences
    sequence seq1;
        @(posedge clk1) y ##1 @(posedge clk1) x;
    endsequence

    sequence seq2;
        @(posedge clk2) x ##0 @(posedge clk2) y;
    endsequence

    // Define assertions using multi-clocked sequences
    property prop1;
        @(posedge clk1) disable iff(!$rose(clk1)) seq1 |-> seq2;
    endproperty

    property prop2;
        @(posedge clk2) disable iff(!$rose(clk2)) seq2 |-> seq1;
    endproperty

    // Apply assertions to DUT signals
    assert property (prop1);
    assert property (prop2);

    // Generate clock signals
    initial begin
        clk1 = 0;
        clk2 = 0;
        forever #5 clk1 = ~clk1;
        forever #10 clk2 = ~clk2;
    end

    // Add simulation termination condition
    initial #100 $finish;
endmodule // mc_14
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 13") {
    auto& text = R"(
`line 1212 "test.sv" 0
property p_inferred_disable(x, y,
			    event ck = $inferred_clock,
			    logic rst = $inferred_disable);
   disable iff (rst) @ck x |=> y;
endproperty

module m_inferred_disable(logic reset, a, b, clk);
   default disable iff reset;
   default clocking @(posedge clk);
   endclocking

   a_inferred_disable: assert property(p_inferred_disable(a, b))
     else $error("FAIL");
endmodule

module mc_15(input clk, en, output dout);
   logic d1, i1, i2, i3, i4;
    always @(posedge clk iff en) begin
        d1 <= i1|i2;
        a4: assert property (d1 |=> i3|i4);
    end
endmodule // mc_15

module mc_16(input clk, en, output dout);
   logic d1, i1, i2, i3, i4;
    always @(clk) begin
        d1 <= i1|i2;
        a4: assert property (d1 |=> i3|i4);
    end
endmodule // mc_16

module m_ss #(parameter int bothedges = 1)
   (input logic  clk);
   if (bothedges) begin :L
   end
   else begin :L
      default clocking dclk @(posedge clk); endclocking
   end

   reg x;
   assert property (x);
endmodule : m_ss

module m_s_17 #(parameter int bothedges = 1)
   (input logic  clk);
   if (bothedges) begin :L
   end
   else begin :L
      default clocking dclk @(posedge clk); endclocking
   end

   reg x;
   assert property (x);
endmodule : m_s_17

module mc_17 (input clk1);
   m_s_17 #(0) seqpot1(clk1);
   m_s_17 #(1) seqpot2(clk2);
endmodule // mc_17

module m_s_18 #(parameter int bothedges = 1)
   (input logic  clk);

   if (bothedges) begin :L
   end
   else begin :L
      default clocking dclk @(posedge clk); endclocking
   end

   reg x;
   assert property (x);
endmodule : m_s_18

module mc_18 (input clk1);
   m_s_18 #(0) seqpot1(clk1);
endmodule // mc_18

module mc_20(input e1, e2, reset, output dout);
   logic d1, i1, i2, i3, i4;
   logic e1N;
   logic sL, sL1, egL;
   always @(posedge e1) begin
      d1 <= i1|i2 ;
      @(posedge e2) egL <= sL & sL1;
      a11: assert property (d1 |=> i3|i4);
   end
endmodule // mc_20

module mc_21(input e1, e2, reset, output dout);
   logic d1, i1, i2, i3, i4;
   always @(posedge e1) begin
      d1 <= i1|i2 ;
      #6;
      a12: assert property (d1 |=> i3|i4);
   end
endmodule // mc_21
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::AssertionNoClock);
    CHECK(diags[3].code == diag::AssertionNoClock);
    CHECK(diags[4].code == diag::AssertionNoClock);
}

TEST_CASE("Clock resolution tests 14 - checkers tests") {
    auto& text = R"(
`line 1326 "test.sv" 0
checker check_01(a, b, c, event clk = $inferred_clock);
    default clocking @clk;
    endclocking
    always_ff @clk begin
        a1: assert property(a);
        a2: assert property(b |=> c);
    end
endchecker : check_01

module m_01(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_01 mycheck(ok, req[i], ack[i]);
	  end
   end
endmodule :m_01

checker check_02(a, b, c, event clk = $inferred_clock);
  always_ff @clk begin
    a1: assert property(a);
    a2: assert property(b |=> c);
  end
endchecker : check_02

module m_02(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_01 mycheck(ok, req[i], ack[i]);
	  end
   end
endmodule :m_02

checker check_03(a, b, c, event clk = $inferred_clock);
    default clocking @clk;
    endclocking
    always_comb begin
        a1: assert property(a);
        a2: assert property(b |=> c);
    end
endchecker : check_03

module m_03(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_03 mycheck(ok, req[i], ack[i]);
	  end
   end
endmodule :m_03

checker check_04(a, b, c, event clk = $inferred_clock);
    always_comb begin
        a1: assert property(a);
        a2: assert property(b |=> c);
    end
endchecker : check_04

module m_04(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_04 mycheck(ok, req[i], ack[i]);
	  end
   end
endmodule :m_04

checker check_05(a, b, c, event clk);
    default clocking @clk;
    endclocking

    always_ff @clk begin
        a1: assert property(a);
        a2: assert property(b |=> c);
    end
endchecker : check_05

module m_05(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_05 mycheck(ok, req[i], ack[i], (posedge clock) );
	  end
   end
endmodule :m_05

module m_06(input e1, e2, reset, output dout);
   logic d1, i1, i2, i3, i4;
   logic e1N;
    always @(posedge((e1|e2)& reset)) begin
        d1 <= i1|i2;
        e1N = ~e1;
        a7: assert property (d1 |=> i3|i4);
    end
endmodule // m_06

module m_07(input e1, e2, reset, output dout);
   logic d1, i1, i2, i3, i4;
   logic e1N;
    always @(posedge(e1|e2)) begin
        d1 <= i1|i2;
        a8_1: assert property (d1 |=> i3|i4);
    end

    always @(posedge(e1|e2) iff reset) begin
        d1 <= i1|i2;
        e1N = ~e1;
        a7: assert property (d1 |=> i3|i4);
    end
endmodule // m_07

module m_08(input e1, e2, reset, output dout);
   reg 	b1, b2;
   sequence a1;
      (@(posedge (e1 | e2)) b1) and (@(posedge (e1 | e2)) b2);
   endsequence // a1

   assert property(a1);

   sequence a2;
      (@(posedge (e1 | e2)) b1) and (@(posedge e1) b2);
   endsequence // a2

   assert property(a2);

   sequence a3;
      (@(posedge (e1 | e2)) b1) and (@(posedge (e1 | e2) iff reset) b2);
   endsequence // a2

   assert property(a3);
endmodule // m_08

checker check_09(a, b, c, d, event clk = $inferred_clock);
    default clocking @(b);
    endclocking
    always_ff @clk begin
        a1: assert property( a and @(posedge b) b);
        a2: assert property(b |=> c);
    end
endchecker : check_09

module m_09(input logic clock, ok, rst, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
	    if (i != 3) begin
	      check_09 mycheck(ok, rst, req[i], ack[i]);
	  end
   end
endmodule : m_09

checker check(a, b, c, event clk = $inferred_clock);
    default clocking @clk;
    endclocking
    always_ff @clk begin
        a1: assert property(a);
        a2: assert property(b |=> c);
    end
endchecker : check

module m_10(input logic clock, ok, logic [7:0] req, ack);
   always @(posedge clock) begin
      for (int i=0;i<8;i++)
           if (i != 3) begin
               check mycheck(ok, req[i], ack[i]);
           end
      end
endmodule :m_10
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
    CHECK(diags[2].code == diag::AssertionNoClock);
    CHECK(diags[3].code == diag::AssertionNoClock);
    CHECK(diags[4].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[5].code == diag::InvalidMulticlockedSeqOp);
    CHECK(diags[6].code == diag::NoUniqueClock);
}

TEST_CASE("Clock resolution tests 15") {
    auto& text = R"(
`line 1506 "test.sv" 0
module mm_01(input clk, a, b);
   property p_no_clock; a|=> b; endproperty : p_no_clock
   property p_with_one_clock; @(posedge clk) a|=> b; endproperty : p_with_one_clock

   p_no_clock_1: assert property(@(posedge clk)p_no_clock);
   p_with_one_clock_1: assert property(p_with_one_clock);
   p_with_one_clock_1a: assert property(@(posedge clk)p_with_one_clock);
endmodule // mm_01

module mm_02(input clk, a, b);
   property p_no_clock; a|=> b; endproperty : p_no_clock
   property p_with_one_clock; @(posedge clk) a|=> b; endproperty : p_with_one_clock

   always @(posedge clk) begin
      p_no_clock_1: assert property(p_no_clock);
      p_with_one_clock_1: assert property(p_with_one_clock);
   end
endmodule // mm_02

module mm_03(input clk, a, b);
   property p_no_clock; a|=> b; endproperty : p_no_clock
   property p_with_one_clock; @(posedge clk) a|=> b; endproperty : p_with_one_clock

   clocking sys_clk @(posedge clk); endclocking :sys_clk
   default clocking sys_clk;

   p_no_clock_1: assert property(p_no_clock);
   p_with_one_clock_1: assert property(p_with_one_clock);
endmodule // mm_03

module mm_04(input clk, a, b);
   clocking sys_clk @(posedge clk);
      property p_no_clock; a|=> b; endproperty : p_no_clock
   endclocking :sys_clk
endmodule // mm_04

module mm_06(input clk, clk2, a, b);
   sequence s_with_one_ck;
        @(posedge clk) a;
   endsequence // s_with_one_ck

   sequence s_with_one_ck2;
        @(posedge clk2) b;
   endsequence // s_with_one_ck

   clocking sys_clk @(posedge clk);
      property p_ok; not s_with_one_ck; endproperty
      // If a named sequence that defined outside the clocking block is used, its clock,
      // if specified, must be identical to the clocking block's clock
      property p_not_ok; not s_with_one_ck2; endproperty // illegal
   endclocking :sys_clk
endmodule

module mm_08(input clk, clk1, clk2, a, b);
   property pBadMulticlock;
      a ##1 @(posedge clk2)b;
   endproperty // pBadMulticlock

   property pOkMulticlock;
      @(posedge clk1) a ##1 @(posedge clk2)b;
   endproperty // pOkMulticlock

   always @(posedge clk) assert property(pBadMulticlock); // illegal according SV Assertions Handbook
   initial @(posedge clk2) assert property(pBadMulticlock); // illegal according SV Assertions Handbook
   initial @(posedge clk2) assert property(pOkMulticlock);  // VCS ERR
   initial @(posedge clk1) assert property(pOkMulticlock);
   assert property(pBadMulticlock); // illegal // VCS ERR
   ap_multiclock: assert property(pOkMulticlock);
   always @(clk) assert property(pBadMulticlock); // illegal according SV Assertions Hanbook
   initial @(clk) assert property(pOkMulticlock); // illegal according SV Assertions Hanbook
endmodule // mm_08

module mm_09(input seq_top_clk, s_clk1, s_clk2, start, endtop, a1, b1, c2, d2);
   sequence top_seq;
      @(posedge seq_top_clk) start ##1 sub_seq_1 ##1 sub_seq_2 ##1 endtop; // illegal according SV Assertions Hanbook
      // if seq_top_clk <> s_clk1 and seq_top_clk <> s_clk1
   endsequence // top_seq

   sequence sub_seq_1;
      @(posedge s_clk1) a1 ##1 b1;
   endsequence // sub_seq_1

   sequence sub_seq_2;
      @(posedge s_clk2) c2 ##1 d2;
   endsequence // sub_seq_2

   assert property(top_seq);
endmodule // mm_09
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::AssertionNoClock);
    CHECK(diags[1].code == diag::AssertionNoClock);
}

TEST_CASE("Inferred clock resolution") {
    auto& text = R"(
module m(input clk1, clk2, clk3, a);
    sequence s1 (clk);
        @clk a and @(posedge clk2) a;
    endsequence

    sequence s2 (clk);
        @(clk) a and @(posedge clk1 or negedge clk2) a;
    endsequence

    sequence s3 (clk = $inferred_clock);
        @clk a and @(posedge clk2) a;
    endsequence

    always @(posedge clk1) begin
        assert property (s1(posedge clk2));
        assert property (s2(posedge clk1 or negedge clk2));
        assert property (s3); // illegal
    end

    always @(posedge clk2) begin
        assert property (s3); // ok
    end

    initial begin
        assert property (s3); // illegal
    end

    sequence s4(clk = $inferred_clock);
        @(posedge clk2 or (clk3, posedge clk1)) a and @(posedge clk2 or clk3 or clk) a;
    endsequence

    property p1;
        @(posedge clk1) a and s4;
    endproperty
    assert property (@(posedge clk1) sync_accept_on(a) p1); // legal
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NoInferredClock);
    CHECK(diags[1].code == diag::InvalidMulticlockedSeqOp);
}

TEST_CASE("Basic property with disable iff analysis") {
    auto& text = R"(
module top;
    logic clk1, clk2;
    logic rst_b;
    logic a1, b1, a2, b2;

    property my_prop(clk, rst_b, a, b);
        @(posedge clk) disable iff(~rst_b)
            $rose(a) |-> b;
    endproperty

    prop1: assert property(my_prop(.clk(clk1), .rst_b(rst_b), .a(a1), .b(b1)))
           else $error("%t %m - my_prop failed", $time);

    prop2: assert property(my_prop(.clk(clk2), .rst_b(rst_b), .a(a2), .b(b2)))
           else $error("%t %m - my_prop failed", $time);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Checker default inferred clocks") {
    auto& text = R"(
module top(input clk);
    checker c1(ev);
        default clocking @(posedge clk); endclocking
        sequence s;
            1 and @ev 1;
        endsequence
        assert property (s);
    endchecker

    c1 c1_inst(posedge clk);

    default clocking @(negedge clk); endclocking

    checker c2(ev);
        sequence s;
            1 and @ev 1;
        endsequence
        assert property (s);
    endchecker

    c2 c2_inst(negedge clk);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Checker explicit inferred clocks") {
    auto& text = R"(
module top(input clk);
    checker c1(ev = $inferred_clock);
        sequence s1;
            @(posedge clk) 1 and @ev 1;
        endsequence

        sequence s2(ev1, ev2 = $inferred_clock);
            @ev1 1 and @ev2 1;
        endsequence

        assert property (s1); // uses @ev directly
        assert property (s2(negedge clk)); // uses the default clock

        always_ff @ev begin
            assert property (s1);  // uses @ev directly
            assert property (s2(posedge clk));  // infers from always_ff
        end

        checker c2;
            always_ff @ev begin
            end

            sequence s3(ev1 = $inferred_clock);
                @ev1 1;
            endsequence

            assert property (s3(ev));
            assert property (s3());
        endchecker

        c2 c2_inst();
    endchecker

    default clocking @(negedge clk); endclocking

    always_ff @(posedge clk) begin
        c1 c1_inst();

        assert property (p1);
    end

    sequence s2(ev = $inferred_clock);
        @ev 1 and @(posedge clk) 1;
    endsequence

    property p1(ev = $inferred_clock);
        @ev 1 and @(negedge clk) s2(ev);
    endproperty
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Expect statement in task is analyzed") {
    auto& text = R"(
module test(input clk, a, b, c);

   program tst;
      initial begin
         # 200ms;
         expect( @(posedge clk) a ##1 b ##1 c ) else $error( "expect failed" );
      end
   endprogram

   integer data;

   task automatic wait_for( integer value, output bit success );
      wait (!success) #10 value = 1;
      expect( ##[1:10] data == value ) success = 1;
         else success = 0;
   endtask

   initial begin
      bit ok;
      wait_for( 23, ok );  // wait for the value 23
      // ...
   end

endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(text, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AssertionNoClock);
}
