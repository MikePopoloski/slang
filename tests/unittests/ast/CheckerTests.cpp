// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

TEST_CASE("Checker declarations") {
    auto tree = SyntaxTree::fromText(R"(
checker my_check1 (logic test_sig, event clock);
    default clocking @clock; endclocking
    property p(logic sig); 1; endproperty
    a1: assert property (p (test_sig));
    c1: cover property (!test_sig ##1 test_sig);
endchecker : my_check1

checker my_check2 (logic a, b);
    a1: assert #0 ($onehot0({a, b}));
    c1: cover #0 (a == 0 && b == 0);
    c2: cover #0 (a == 1);
    c3: cover #0 (b == 1);
endchecker : my_check2

checker my_check3 (logic a, b, event clock, output bit failure, undef);
    default clocking @clock; endclocking
    a1: assert property ($onehot0({a, b})) failure = 1'b0; else failure = 1'b1;
    a2: assert property ($isunknown({a, b})) undef = 1'b0; else undef = 1'b1;
endchecker : my_check3

checker my_check4 (input logic in,
                   en = 1'b1, // default value
                   event clock,
                   output int ctr = 0); // initial value
    default clocking @clock; endclocking
    always_ff @clock
        if (en && in) ctr <= ctr + 1;
    a1: assert property (ctr < 5);
endchecker : my_check4

module m;
    wire clk1, clk2, rst1, rst2;

    default clocking @clk1; endclocking
    default disable iff rst1;
    checker c1;
    endchecker : c1
    checker c2;
        default clocking @clk2; endclocking
        default disable iff rst2;
    endchecker : c2
endmodule : m
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checker instantiation") {
    auto tree = SyntaxTree::fromText(R"(
checker mutex (logic [31:0] sig, event clock, output bit failure);
    assert property (@clock $onehot0(sig))
        failure = 1'b0; else failure = 1'b1;
endchecker : mutex

module m1(wire [31:0] bus, logic clk);
    logic res, scan;
    mutex check_bus(bus, posedge clk, res);
    always @(posedge clk) scan <= res;
endmodule : m1

checker c1(event clk, logic[7:0] a, b);
    logic [7:0] sum;
    always_ff @(clk) begin
        sum <= a + 1'b1;
        p0: assert property (sum < 10);
    end
    p1: assert property (@clk sum < 10);
    p2: assert property (@clk a != b);
    p3: assert #0 ($onehot(a));
endchecker

module m2(input logic rst, clk, logic en, logic[7:0] in1, in2,
          in_array [20:0]);
    c1 check_outside(posedge clk, in1, in2);
    always @(posedge clk) begin
        automatic logic [7:0] v1=0;
        if (en) begin
            // v1 is automatic, so current procedural value is used
            c1 check_inside(posedge clk, in1, v1);
        end
        for (int i = 0; i < 4; i++) begin
            v1 = v1+5;
            if (i != 2) begin
                // v1 is automatic, so current procedural value is used
                c1 check_loop(posedge clk, in1, in_array[v1]);
            end
        end
    end
endmodule : m2
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checker formal port error checking") {
    auto tree = SyntaxTree::fromText(R"(
checker c(input i, j[3], local output int k, property p);
endchecker
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CheckerPortDirectionType);
    CHECK(diags[1].code == diag::InvalidArrayElemType);
    CHECK(diags[2].code == diag::LocalNotAllowed);
    CHECK(diags[3].code == diag::CheckerOutputBadType);
}

TEST_CASE("Checker port connections") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    real prq;
    checker c(a, b, output bit c, input real r = prq);
        initial assert(real'(a + b) + r > 1);
        always_comb c = 1;
    endchecker
endpackage

module m;
    bit d;
    initial p::c c1(1, 2, d, 3.14);

    int a, b;
    real r;

    import p::*;
    c c2 [3](1, 2, e, 3.14);
    c c3 [1:2][3:2] (.*, .c(foo), .r);
    c c4(.*, .c(foo));
    c c5(1, 2, e);
    c c6(.a(1), .b, .c(foo));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checker port connection errors") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    real prq;
    bit bc;
    checker c(a, b, output bit c = bc, input real r = prq);
        initial assert(a + b + r > 1);
        always_comb c = 1;

        checker d(input untyped);
        endchecker

        d d1();
    endchecker
endpackage

module m;
    import p::*;
    c c1(1, , 3, 4, 5);
    c c2();
    c c3(.a(), .b(1), .q(3));
    c c4(.*, .c(), .r(), 5);

    int b;

    initial c c5(1, 2, foo);
    c c6(1, 2, bar);

    checker q(output int r = unknown); endchecker
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 19);
    CHECK(diags[0].code == diag::ExpectedIdentifier);
    CHECK(diags[1].code == diag::CheckerArgCannotBeEmpty);
    CHECK(diags[2].code == diag::ExpressionNotAssignable);
    CHECK(diags[3].code == diag::SignConversion);
    CHECK(diags[4].code == diag::WidthExpand);
    CHECK(diags[5].code == diag::TooManyPortConnections);
    CHECK(diags[6].code == diag::UnconnectedArg);
    CHECK(diags[7].code == diag::UnconnectedArg);
    CHECK(diags[8].code == diag::UnconnectedArg);
    CHECK(diags[9].code == diag::UnconnectedArg);
    CHECK(diags[10].code == diag::CheckerArgCannotBeEmpty);
    CHECK(diags[11].code == diag::PortDoesNotExist);
    CHECK(diags[12].code == diag::ImplicitNamedPortNotFound);
    CHECK(diags[13].code == diag::UsedBeforeDeclared);
    CHECK(diags[14].code == diag::CheckerArgCannotBeEmpty);
    CHECK(diags[15].code == diag::CheckerArgCannotBeEmpty);
    CHECK(diags[16].code == diag::MixingOrderedAndNamedPorts);
    CHECK(diags[17].code == diag::UndeclaredIdentifier);
    CHECK(diags[18].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Checker invalid instantiations") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int e;
    function automatic func(int a, b); endfunction
    class cls; endclass
endpackage

checker check;
endchecker

module m;
    c c1(posedge clk, $, 3 + 4);
    initial d d1(posedge clk, $, 3 + 4);

    p::e e1(posedge clk, $, 3 + 4);

    p::func func(1, 2);
    p::cls cls(1, 2);

    check #(1, 2) c2();

    initial begin
        fork : asdf
            if (1) begin : bazz
                check c1();
            end
        join_none
    end

    checker cfoo;
        initial check c4();
    endchecker

    cfoo foo1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::UnknownModule);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::NotAChecker);
    CHECK(diags[3].code == diag::CheckerFuncBadInstantiation);
    CHECK(diags[4].code == diag::CheckerClassBadInstantiation);
    CHECK(diags[5].code == diag::CheckerParameterAssign);
    CHECK(diags[6].code == diag::CheckerInForkJoin);
    CHECK(diags[7].code == diag::CheckerInCheckerProc);
}

TEST_CASE("Assertion ports invalid directions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s(local ref int r); 1; endsequence
    checker c(inout int i); endchecker
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::AssertionPortRef);
    CHECK(diags[1].code == diag::CheckerPortInout);
}

TEST_CASE("Invalid instantiations inside checkers") {
    auto tree = SyntaxTree::fromText(R"(
module m;
endmodule

package p;
endpackage

checker c;
    module n;
    endmodule

    package p2;
    endpackage

    checker c2;
    endchecker

    c2 asdf();
    m m1();
endchecker

checker c2;
    int i = j;
endchecker

module n;
    c c1();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::NotAllowedInChecker);
    CHECK(diags[1].code == diag::InvalidInstanceForParent);
    CHECK(diags[2].code == diag::NotAllowedInChecker);
    CHECK(diags[3].code == diag::InvalidInstanceForParent);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Upward lookup from checkers") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic req, gnt;
endmodule :m

module top;
    logic clock, reset;
    m m1();
    request_granted c1(clock, reset);
endmodule : top

checker request_granted(clk, rst);
    a1: assert property (@clk disable iff (rst) m1.req |=> m1.gnt);
endchecker : request_granted
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Hierarchical lookup into checkers disallowed") {
    auto tree = SyntaxTree::fromText(R"(
checker c(q);
    int i;
endchecker

module m;
    int j = c.i + c.q;
    c c1(3);
    int k = c1.i + c1.q;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CheckerHierarchical);
    CHECK(diags[1].code == diag::CheckerHierarchical);
    CHECK(diags[2].code == diag::CheckerHierarchical);
    CHECK(diags[3].code == diag::CheckerHierarchical);
}

TEST_CASE("Nested checker name lookup") {
    auto tree = SyntaxTree::fromText(R"(
checker c(q);
    int i;
    checker d(r);
        int j = i;
        int k = q + r;
    endchecker

    d d1(q);
endchecker

module m;
    c c1(3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive checker instances -- ok") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    checker c(q);
        if (q < 4) begin
            c c_next(q + 1);
            p::c c_next2(q + 1);
        end
    endchecker
endpackage

module m;
    p::c c1(1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Recursive checker instances -- bad") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    checker c(q);
        c c_next(q + 1);
    endchecker
endpackage

module m;
    p::c c1(1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MaxInstanceDepthExceeded);
}

TEST_CASE("Checkers diagnostic expansion stack") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    checker c(q);
        d d1(q);
    endchecker

    checker d(r);
        string a;
        logic b,c,d,e;

        assert property (a ##1 b ##[+] c ##[*] d ##[1:5] e & r);
    endchecker
endpackage

module m;
    p::c c1(1);
    p::c c2($);

    checker e(q);
        f f1(q);
    endchecker

    checker f(r);
        int foo[$];
        int j = foo + r;
    endchecker

    e e1(5);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diagnostics = compilation.getAllDiagnostics();
    std::string result = "\n" + report(diagnostics);
    CHECK(result == R"(
source:17:13: error: unbounded literal '$' not allowed here
    p::c c2($);
            ^
source:4:14: note: expanded here
        d d1(q);
             ^
source:11:62: note: expanded here
        assert property (a ##1 b ##[+] c ##[*] d ##[1:5] e & r);
                                                             ^
source:25:21: error: invalid operands to binary expression ('queue of int' and 'int')
        int j = foo + r;
                ~~~ ^ ~
source:20:11: note: while expanding checker 'f'
        f f1(q);
          ^
source:28:7: note: while expanding checker 'e'
    e e1(5);
      ^
)");
}

TEST_CASE("Binding checker targets") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    checker c(q);
    endchecker
endpackage

module m;
    import p::*;
endmodule

module n;
    m m1();
    bind m c c1(1);
    bind m p::c c2(1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Binding checker errors") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    checker c(q);
    endchecker
endpackage

module m;
    import p::*;
endmodule

module n;
    m m1();
    bind m o o1();
    bind o p::c c1(1);
endmodule

module o;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BindUnderBind);
}

TEST_CASE("UDNT decl in checker") {
    auto tree = SyntaxTree::fromText(R"(
nettype logic l;
checker s;
    l r;
endchecker
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NotAllowedInChecker);
}

TEST_CASE("Inferred value sys funcs in checkers") {
    auto tree = SyntaxTree::fromText(R"(
checker check_in_context (logic test_sig,
                          event clock = $inferred_clock,
                          logic reset = $inferred_disable);
    property p(logic sig); 1; endproperty
    a1: assert property (@clock disable iff (reset) p(test_sig));
    c1: cover property (@clock !reset throughout !test_sig ##1 test_sig);
endchecker : check_in_context

module m(logic rst);
    wire clk;
    logic a, en;
    wire b = a && en;

    // No context inference
    check_in_context my_check1(.test_sig(b), .clock(clk), .reset(rst));

    always @(posedge clk) begin
        a <= 1;
        if (en) begin
            // inferred from context:
            // .clock(posedge clk)
            // .reset(1'b0)
            check_in_context my_check2(a);
        end
        en <= 1;
    end
endmodule : m
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroups in checkers") {
    auto tree = SyntaxTree::fromText(R"(
checker my_check(logic clk, active);
    bit active_d1 = 1'b0;
    always_ff @(posedge clk) begin
        active_d1 <= active;
    end

    covergroup cg_active @(posedge clk);
        cp_active : coverpoint active
        {
            bins idle = { 1'b0 };
            bins active = { 1'b1 };
        }
        cp_active_d1 : coverpoint active_d1
        {
            bins idle = { 1'b0 };
            bins active = { 1'b1 };
        }
        option.per_instance = 1;
    endgroup
    cg_active cg_active_1 = new();
endchecker : my_check

checker op_test1 (logic clk, vld_1, vld_2, logic [3:0] opcode);
    bit [3:0] opcode_d1;

    always_ff @(posedge clk) opcode_d1 <= opcode;

    covergroup cg_op;
        cp_op : coverpoint opcode_d1;
    endgroup: cg_op
    cg_op cg_op_1 = new();

    sequence op_accept;
        @(posedge clk) vld_1 ##1 (vld_2, cg_op_1.sample());
    endsequence
    cover property (op_accept);
endchecker

checker op_test2 (logic clk, vld_1, vld_2, logic [3:0] opcode);
    bit [3:0] opcode_d1;

    always_ff @(posedge clk) opcode_d1 <= opcode;

    covergroup cg_op with function sample(bit [3:0] opcode_d1);
        cp_op : coverpoint opcode_d1;
    endgroup: cg_op
    cg_op cg_op_1 = new();

    sequence op_accept;
        @(posedge clk) vld_1 ##1 (vld_2, cg_op_1.sample(opcode_d1));
    endsequence
    cover property (op_accept);
endchecker

module m;
    logic clk;
    my_check c1(clk, 1);
    op_test1 t1(clk, 1, 1, 3);
    op_test2 t2(clk, 1, 1, 3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checker LRM examples") {
    auto tree = SyntaxTree::fromText(R"(
typedef enum { cover_none, cover_all } coverage_level;
checker assert_window1 (
    logic test_expr,
    untyped start_event,
    untyped end_event,
    event clock = $inferred_clock,
    logic reset = $inferred_disable,
    string error_msg = "violation",
    coverage_level clevel = cover_all
);
    default clocking @clock; endclocking
    default disable iff reset;
    bit window = 1'b0, next_window = 1'b1;

    always_comb begin
        if (reset || (window && end_event))
            next_window = 1'b0;
        else if (!window && start_event)
            next_window = 1'b1;
        else
            next_window = window;
    end

    always_ff @clock
        window <= next_window;

    property p_window;
        start_event && !window |=> test_expr[+] ##0 end_event;
    endproperty

    a_window: assert property (p_window) else $error(error_msg);

    generate if (clevel != cover_none) begin : cover_b
        cover_window_open: cover property (start_event && !window)
        $display("window_open covered");
        cover_window: cover property (
            start_event && !window
            ##1 (!end_event && window) [*]
            ##1 end_event && window
        ) $display("window covered");
    end : cover_b
    endgenerate
endchecker : assert_window1

checker assert_window2 (
    logic test_expr,
    sequence start_event,
    sequence end_event,
    event clock = $inferred_clock,
    logic reset = $inferred_disable,
    string error_msg = "violation",
    coverage_level clevel = cover_all
);
    default clocking @clock; endclocking
    default disable iff reset;
    bit window = 0;
    let start_flag = start_event.triggered;
    let end_flag = end_event.triggered;

    function bit next_window (bit win);
        if (reset || (win && end_flag))
            return 1'b0;
        if (!win && start_flag)
            return 1'b1;
        return win;
    endfunction

    always_ff @clock
        window <= next_window(window);

    property p_window;
        start_flag && !window |=> test_expr[+] ##0 end_flag;
    endproperty

    a_window: assert property (p_window) else $error(error_msg);

    generate if (clevel != cover_none) begin : cover_b
        cover_window_open: cover property (start_flag && !window)
        $display("window_open covered");
        cover_window: cover property (
            start_flag && !window
            ##1 (!end_flag && window) [*]
            ##1 end_flag && window
        ) $display("window covered");
    end : cover_b
    endgenerate
endchecker : assert_window2

checker counter_model(logic flag);
    bit [2:0] counter = '0;
    always_ff @$global_clock
        counter <= counter + 1'b1;
    assert property (@$global_clock counter == 0 |-> flag);
endchecker : counter_model
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Error checking for procedures inside checkers") {
    auto tree = SyntaxTree::fromText(R"(
wire clk;

function void foo(); endfunction

checker s;
    int i;
    final begin
        i++;
    end

    always @(posedge clk) begin end

    initial begin
        fork join_none
        #3 i++;
        @(posedge clk) i++;
    end

    always_comb begin
        i <= 3;
        i = 4;
        if (i > 3) begin
            foo();
        end
    end

    always_ff begin
        @(posedge clk) i = 5;
        fork join_any
        #3 i++;
    end

    always_latch begin
        i++;
    end

    always_comb disable fork;
endchecker
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::AlwaysInChecker);
    CHECK(diags[1].code == diag::InvalidStmtInChecker);
    CHECK(diags[2].code == diag::CheckerTimingControl);
    CHECK(diags[3].code == diag::InvalidStmtInChecker);
    CHECK(diags[4].code == diag::CheckerBlockingAssign);
    CHECK(diags[5].code == diag::InvalidStmtInChecker);
    CHECK(diags[6].code == diag::CheckerTimingControl);
    CHECK(diags[7].code == diag::BlockingInAlwaysFF);
    CHECK(diags[8].code == diag::InvalidStmtInChecker);
    CHECK(diags[9].code == diag::InvalidStmtInChecker);
}

TEST_CASE("Checker variables") {
    auto tree = SyntaxTree::fromText(R"(
checker observer_model(bit valid, reset);
    default clocking @$global_clock; endclocking
    rand bit flag;
    m1: assume property (reset |=> !flag);
    m2: assume property (!reset && flag |=> flag);
    m3: assume property ($rising_gclk(flag) |-> valid);
endchecker : observer_model

checker reason_about_one_bit(bit [63:0] data1, bit [63:0] data2,
                             event clock);
    rand const bit [5:0] idx;
    a1: assert property (@clock data1[idx] == data2[idx]);
endchecker : reason_about_one_bit

checker reason_about_all_bit(bit [63:0] data1, bit [63:0] data2,
                             event clock);
    a1: assert property (@clock data1 == data2);
endchecker : reason_about_all_bit

wire clock;
checker data_legal(start_ev, end_ev, in_data, out_data);
    rand const bit [$bits(in_data)-1:0] mem_data;
    sequence transaction;
        start_ev && (in_data == mem_data) ##1 end_ev[->1];
    endsequence
    a1: assert property (@clock transaction |-> out_data == mem_data);
endchecker : data_legal

checker data_legal_with_loc(start_ev, end_ev, in_data, out_data);
    sequence transaction (loc_var);
        (start_ev, loc_var = in_data) ##1 end_ev[->1];
    endsequence

    property data_legal;
        bit [$bits(in_data)-1:0] mem_data;
        transaction(mem_data) |-> out_data == mem_data;
    endproperty

    a1: assert property (@clock data_legal);
endchecker : data_legal_with_loc
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Checker variable errors") {
    auto tree = SyntaxTree::fromText(R"(
checker check1(bit a, b, event clk);
    rand bit x, y, z, v;
    assign x = a & b; // Illegal
    always_comb
        y = a & b; // Illegal
    always_ff @clk
        z <= a & b; // OK

    initial v = 1'b0; // Illegal
    bit w = 1'b0; // OK
endchecker : check1

module m;
    wire clk;
    check1 c(1, 0, clk);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::BlockingAssignToFreeVar);
    CHECK(diags[1].code == diag::BlockingAssignToFreeVar);
    CHECK(diags[2].code == diag::BlockingAssignToFreeVar);
}

TEST_CASE("Checker function restrictions") {
    auto tree = SyntaxTree::fromText(R"(
int i;

function automatic int f1(output int o);
    return 1;
endfunction

function automatic int f2(const ref int o);
    return 1;
endfunction

module m;
    int j;
    checker check1(bit a, b, event clk);
        int k;
        always_comb begin
            i = f1(i);
            j = f1(i);
            k = f1(i);
            k = f2(i);
        end
    endchecker

    wire clk;
    check1 c(1, 0, clk);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CheckerFuncArg);
}

TEST_CASE("Checker dynamic access restrictions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    class C;
        int i;
    endclass

    C c;
    int d[];

    initial
        fork : h
            int d;
        join

    checker e;
        int a = c.i;
        int b = d[0];
        int e[];
        int f = e[0];
        int g = h.d;
    endchecker
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::DynamicFromChecker);
    CHECK(diags[1].code == diag::DynamicFromChecker);
    CHECK(diags[2].code == diag::CheckerForkJoinRef);
}

TEST_CASE("Checker instantiation infinite loop regress 1") {
    auto tree = SyntaxTree::fromText("checker\0module w\0w("sv);

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no crashes.
    compilation.getAllDiagnostics();
}

TEST_CASE("Checker instantiation infinite loop regress 2") {
    auto tree = SyntaxTree::fromText("checker a a(;a(endchecker a("sv);

    CompilationOptions options;
    options.maxCheckerInstanceDepth = 16;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    // Just check no crashes.
    compilation.getAllDiagnostics();
}

TEST_CASE("Checker instantiation infinite loop regress 3") {
    auto tree = SyntaxTree::fromText(R"(
checker a waty (p_window) else $error(error_msg);

module m5;
    a aw1(1ss
endmodule

a aw1(1ss
)");

    CompilationOptions options;
    options.maxCheckerInstanceDepth = 16;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    // Just check no crashes.
    compilation.getAllDiagnostics();
}

TEST_CASE("Checker port binding crash regress") {
    auto tree = SyntaxTree::fromText(R"(
checker(_e,[_e
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no crashes.
    compilation.getAllDiagnostics();
}

TEST_CASE("Rules for checker args with automatic vars, const casts") {
    auto tree = SyntaxTree::fromText(R"(
module m(input clk);
    checker c(a, b, e);
        bit c;
        always_comb c = a;

        bit d;
        assign d = b;

        covergroup cg;
            coverpoint e;
        endgroup
    endchecker

    logic foo[4];
    initial begin
        automatic int bar;
        c c1(foo[bar], 1 + const'(foo[0]), 1 + const'(foo[1]));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::CheckerAutoVarRef);
    CHECK(diags[1].code == diag::CheckerConstCast);
    CHECK(diags[2].code == diag::CheckerConstCast);
}

TEST_CASE("Covergroups in procedural block in checker") {
    auto tree = SyntaxTree::fromText(R"(
module m(input clk);
    checker c;
        covergroup cg;
        endgroup

        cg cg1 = new;
        always_comb begin
            cg1.sample();
        end
    endchecker

    initial begin
        c c1();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CheckerCovergroupProc);
}
