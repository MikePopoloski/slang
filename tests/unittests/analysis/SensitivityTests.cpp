// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

// Owns a Compilation + AnalysisManager pair, runs analysis on the supplied code
// snippet, asserts no diagnostics, and exposes the resulting procedures.
struct SensitivityHarness {
    Compilation compilation;
    AnalysisManager analysisManager;
    std::vector<const AnalyzedProcedure*> procs;

    SensitivityHarness(std::string_view code, AnalysisOptions options = {}) :
        analysisManager(options) {
        analysisManager.addListener([this](const AnalyzedProcedure& proc) {
            if (proc.analyzedSymbol->kind != SymbolKind::Subroutine)
                procs.push_back(&proc);
        });
        auto diags = analyze(std::string(code), compilation, analysisManager);
        CHECK_DIAGS_EMPTY;
    }

    SensitivityList sensitivity(size_t idx = 0) const {
        REQUIRE(procs.size() > idx);
        return procs[idx]->getSensitivityList();
    }
};

// Checks that the read-set of a sensitivity list contains exactly the supplied
// signal names (order-insensitive).
static void checkSensitivityNames(const SensitivityList& sensit,
                                  std::initializer_list<std::string_view> expected) {
    std::set<std::string_view> names;
    for (auto& rr : sensit.reads)
        names.insert(rr.symbol->name);
    CHECK(names == std::set<std::string_view>(expected));
}

using SLK = SensitivityList::Kind;

TEST_CASE("Sensitivity list - always_comb") {
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    always_comb begin
        y = a & b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always_latch") {
    SensitivityHarness h(R"(
module m;
    logic en, d, q;
    always_latch begin
        if (en)
            q = d;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"en", "d"});
}

TEST_CASE("Sensitivity list - always_ff explicit") {
    SensitivityHarness h(R"(
module m(input logic clk);
    logic [7:0] count;
    always_ff @(posedge clk) begin
        count <= count + 1;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Explicit);
    REQUIRE(sensit.timingControl != nullptr);
    CHECK(sensit.timingControl->kind == TimingControlKind::SignalEvent);
    checkSensitivityNames(sensit, {"clk"});
}

TEST_CASE("Sensitivity list - always with explicit event list") {
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    always @(a or b) begin
        y = a & b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Explicit);
    REQUIRE(sensit.timingControl != nullptr);
    CHECK(sensit.timingControl->kind == TimingControlKind::EventList);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always @*") {
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    always @(*) begin
        y = a & b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always @* lvalue-only signal excluded") {
    SensitivityHarness h(R"(
module m;
    logic a, y;
    always @(*) begin
        y = a;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - always @* read-write signal stays in sensitivity") {
    SensitivityHarness h(R"(
module m;
    logic a, y;
    always @(*) y = y ^ a;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    // y is read on the RHS, so it IS in the sensitivity list.
    // (always_comb would exclude y because it is also driven; @* does not.)
    checkSensitivityNames(sensit, {"a", "y"});
}

TEST_CASE("Sensitivity list - always @* timing-control identifier excluded") {
    SensitivityHarness h(R"(
module m;
    logic clk, a, b, y;
    always @(*) begin
        y = a;
        @(posedge clk)
            y = b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always @* vs always_comb function body reads") {
    auto& combCode = R"(
module m;
    logic a, b, y;
    function logic f(input logic x);
        return x & b;
    endfunction
    always_comb y = f(a);
endmodule
)";

    auto& starCode = R"(
module m;
    logic a, b, y;
    function logic f(input logic x);
        return x & b;
    endfunction
    always @(*) y = f(a);
endmodule
)";

    // --- always_comb: should see both a and b ---
    {
        SensitivityHarness h(combCode);
        auto sensit = h.sensitivity();
        CHECK(sensit.kind == SLK::Implicit);
        checkSensitivityNames(sensit, {"a", "b"});
    }

    // --- always @*: should see only a, not b ---
    {
        SensitivityHarness h(starCode);
        auto sensit = h.sensitivity();
        CHECK(sensit.kind == SLK::Implicit);
        checkSensitivityNames(sensit, {"a"});
    }
}

TEST_CASE("Sensitivity list - initial block has no sensitivity") {
    SensitivityHarness h(R"(
module m;
    logic a;
    initial begin
        a = 1;
    end
endmodule
)");
    CHECK(h.sensitivity().kind == SLK::None);
}

TEST_CASE("Sensitivity list - locals excluded from always_comb") {
    // 'temp' is a static local variable; it must not appear in the sensitivity
    // list even though it is read on the RHS.  Only the external input 'a'
    // should be present.
    SensitivityHarness h(R"(
module m;
    logic a, y;
    always_comb begin
        static logic temp = 0;
        y = a | temp;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - always @* static local excluded") {
    SensitivityHarness h(R"(
module m;
    logic a, y;
    always @(*) begin
        static logic temp;
        temp = a;       // reads 'a' (external), writes 'temp' (local)
        y = temp;       // reads 'temp' (local, must be excluded)
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - continuous assignment") {
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    assign y = a & b;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always_comb written signal excluded") {
    SensitivityHarness h(R"(
module m;
    logic a, y;
    always_comb y = y ^ a;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - always_comb partially driven vector") {
    // vec[3:0] is written; vec[7:4] is only read.
    // Only the undriven half should appear in the sensitivity list.
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic [3:0] y;
    always_comb begin
        vec[3:0] = 4'h0;         // drives bits [3:0]
        y = vec[7:4];            // reads bits [7:4]
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 4);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - always_comb function-driven signal excluded") {
    SensitivityHarness h(R"(
module m;
    logic a, y, tmp;
    function void compute(input logic x);
        tmp = x;
    endfunction
    always_comb begin
        compute(a);
        y = tmp;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - always_comb partial select (LSP)") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic y;
    always_comb begin
        y = vec[3:1];
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 1);
    CHECK(sensit.reads[0].bitRange.second == 3);
}

TEST_CASE("Sensitivity list - always_comb nets (wires)") {
    SensitivityHarness h(R"(
module m(input wire a, input wire b, output logic y);
    always_comb begin
        y = a & b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always_comb class instance method body not inlined") {
    SensitivityHarness h(R"(
module m;
    class MyClass;
        logic x;
        function logic get(logic v);
            return v & x;
        endfunction
    endclass
    MyClass obj = new;
    logic a, result;
    always_comb begin
        result = obj.get(a);
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "obj"});
}

TEST_CASE("Sensitivity list - always_comb static class method inlines body reads") {
    // A static class method referenced via the scope-resolution operator
    // behaves like a plain function: its body reads are inlined into the
    // caller's implicit sensitivity list.
    SensitivityHarness h(R"(
module m;
    logic ext_sig;
    class MyClass;
        static function logic compute(logic v);
            return v & ext_sig;
        endfunction
    endclass
    logic a, result;
    always_comb begin
        result = MyClass::compute(a);
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "ext_sig"});
}

TEST_CASE("Sensitivity list - always @* delay expression excluded") {
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    logic [7:0] dly;
    always @(*) begin
        y = a;
        #dly
        y = b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always_comb immediate assertion condition contributes") {
    SensitivityHarness h(R"(
module m;
    logic b, c, e, disable_error;
    logic a;
    always_comb begin
        a = b & c;
        A1: assert (a != e) else if (!disable_error) $error("failed");
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"b", "c", "e"});
}

// ---------------------------------------------------------------------------
// Wait-statement timing-control expressions (LRM 9.4.2.5)
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - always @* wait condition excluded") {
    SensitivityHarness h(R"(
module m;
    logic done, a, b, y;
    always @(*) begin
        y = a;
        wait (done)
            y = b;
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

TEST_CASE("Sensitivity list - always @* wait_order events excluded") {
    SensitivityHarness h(R"(
module m;
    event e1, e2;
    logic a, y;
    always @(*) begin
        y = a;
        wait_order (e1, e2);
    end
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

// ---------------------------------------------------------------------------
// Continuous-assign function-body inlining
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - continuous assign default") {
    // Default behaviour (flag not set): the sensitivity of an assign covers only
    // signals directly visible in the assignment expression. Function-body reads
    // are NOT expanded, consistent with always @* semantics.
    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    function logic f(input logic x);
        return x & b;   // b is an upward reference inside the function
    endfunction
    assign y = f(a);
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a"});
}

TEST_CASE("Sensitivity list - continuous assign with flag") {
    AnalysisOptions opts;
    opts.flags |= AnalysisFlags::InlineContAssignFunctionReads;

    SensitivityHarness h(R"(
module m;
    logic a, b, y;
    function logic f(input logic x);
        return x & b;
    endfunction
    assign y = f(a);
endmodule
)",
                         opts);
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"a", "b"});
}

// ---------------------------------------------------------------------------
// Struct / union member partial-select sensitivity
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - always_comb packed struct member read") {
    SensitivityHarness h(R"(
module m;
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } packed_t;
    packed_t s;
    logic [3:0] y;
    always_comb y = s.hi;   // only the upper nibble is read
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 4);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - always_comb packed struct two members read") {
    SensitivityHarness h(R"(
module m;
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } packed_t;
    packed_t s;
    logic [7:0] y;
    always_comb y = {s.hi, s.lo};
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - always_comb union member read") {
    SensitivityHarness h(R"(
module m;
    typedef union packed {
        logic [7:0] bytes;
        struct packed { logic [3:0] hi; logic [3:0] lo; } nibbles;
    } union_t;
    union_t u;
    logic [7:0] y;
    always_comb y = u.bytes;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"u"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

// ---------------------------------------------------------------------------
// Array element-select sensitivity
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - assign array constant index") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] arr [0:3];
    logic [7:0] y;
    assign y = arr[2];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"arr"});
}

TEST_CASE("Sensitivity list - assign array variable index") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] arr [0:3];
    logic [1:0] idx;
    logic [7:0] y;
    assign y = arr[idx];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"arr", "idx"});
}

TEST_CASE("Sensitivity list - always_comb array constant index") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] arr [0:3];
    logic [7:0] y;
    always_comb y = arr[1];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"arr"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 8);
    CHECK(sensit.reads[0].bitRange.second == 15);
}

TEST_CASE("Sensitivity list - always_comb array variable index") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] arr [0:3];
    logic [1:0] idx;
    logic [7:0] y;
    always_comb y = arr[idx];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"arr", "idx"});
}

TEST_CASE("Sensitivity list - always @* array variable index") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] arr [0:3];
    logic [1:0] idx;
    logic [7:0] y;
    always @(*) y = arr[idx];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"arr", "idx"});
}

// ---------------------------------------------------------------------------
// always @* identifier vs LSP sensitivity
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - always @* constant bit-select default") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic out;
    always @(*) out = vec[5];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - always @* constant bit-select with flag") {
    AnalysisOptions opts;
    opts.flags = AnalysisFlags::AlwaysStarUsesLSPs;

    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic out;
    always @(*) out = vec[5];
endmodule
)",
                         opts);
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 5);
    CHECK(sensit.reads[0].bitRange.second == 5);
}

TEST_CASE("Sensitivity list - always @* multiple selects collapse") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic [1:0] out;
    always @(*) out = {vec[5], vec[2]};
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    CHECK(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

// ---------------------------------------------------------------------------
// assign identifier vs LSP sensitivity
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - assign constant bit-select default") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic out;
    assign out = vec[5];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - assign constant bit-select with flag") {
    AnalysisOptions opts;
    opts.flags = AnalysisFlags::ContAssignUsesLSPs;

    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic out;
    assign out = vec[5];
endmodule
)",
                         opts);
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 5);
    CHECK(sensit.reads[0].bitRange.second == 5);
}

TEST_CASE("Sensitivity list - always_comb bit-select still uses LSP") {
    SensitivityHarness h(R"(
module m;
    logic [7:0] vec;
    logic out;
    always_comb out = vec[5];
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"vec"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 5);
    CHECK(sensit.reads[0].bitRange.second == 5);
}

// ---------------------------------------------------------------------------
// Unpacked struct / union sensitivity
// ---------------------------------------------------------------------------

TEST_CASE("Sensitivity list - always_comb unpacked struct member read") {
    SensitivityHarness h(R"(
module m;
    typedef struct {
        logic [3:0] a;
        logic [3:0] b;
    } unpacked_t;
    unpacked_t s;
    logic [3:0] y;
    always_comb y = s.b;   // only field 'b' is read
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 4);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - always_comb unpacked struct first member read") {
    SensitivityHarness h(R"(
module m;
    typedef struct {
        logic [3:0] a;
        logic [3:0] b;
    } unpacked_t;
    unpacked_t s;
    logic [3:0] y;
    always_comb y = s.a;   // only field 'a' is read
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 3);
}

TEST_CASE("Sensitivity list - always_comb unpacked struct two members read") {
    SensitivityHarness h(R"(
module m;
    typedef struct {
        logic [3:0] a;
        logic [3:0] b;
    } unpacked_t;
    unpacked_t s;
    logic [7:0] y;
    always_comb y = {s.b, s.a};
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
}

TEST_CASE("Sensitivity list - always_comb unpacked union member read") {
    SensitivityHarness h(R"(
module m;
    typedef union {
        logic [3:0] x;
        logic [7:0] y;
    } union_t;
    union_t u;
    logic [3:0] z;
    always_comb z = u.x;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"u"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 3);
}

TEST_CASE("Sensitivity list - assign unpacked struct member read") {
    SensitivityHarness h(R"(
module m;
    typedef struct {
        logic [3:0] a;
        logic [3:0] b;
    } unpacked_t;
    unpacked_t s;
    logic [3:0] y;
    assign y = s.b;
endmodule
)");
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 0);
    CHECK(sensit.reads[0].bitRange.second == 7);
}

TEST_CASE("Sensitivity list - assign unpacked struct member read with flag") {
    AnalysisOptions opts;
    opts.flags = AnalysisFlags::ContAssignUsesLSPs;

    SensitivityHarness h(R"(
module m;
    typedef struct {
        logic [3:0] a;
        logic [3:0] b;
    } unpacked_t;
    unpacked_t s;
    logic [3:0] y;
    assign y = s.b;
endmodule
)",
                         opts);
    auto sensit = h.sensitivity();
    CHECK(sensit.kind == SLK::Implicit);
    checkSensitivityNames(sensit, {"s"});
    REQUIRE(sensit.reads.size() == 1);
    CHECK(sensit.reads[0].bitRange.first == 4);
    CHECK(sensit.reads[0].bitRange.second == 7);
}
