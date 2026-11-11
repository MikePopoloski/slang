// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

// Returns one "line:column: message" entry per warning of the DFFName check.
static std::string getDFFNameWarnings(std::string_view code, const TidyConfig& config = {}) {
    std::string output;
    runCheckTest("DFFName", code, config, &output);

    std::string warnings;
    std::istringstream lines(output);
    for (std::string line; std::getline(lines, line);) {
        const auto warningStart = line.find(" warning: [STYLE-37] ");
        if (line.starts_with("source:") && warningStart != std::string::npos) {
            warnings += line.substr(7, warningStart - 7) +
                        line.substr(warningStart + sizeof(" warning: [STYLE-37]") - 1) + "\n";
        }
    }
    return warnings;
}

TEST_CASE("DFFName: Default suffixes are accepted") {
    auto result = runCheckTest("DFFName", R"(
interface bus_if;
    logic data_q, data_d;
endinterface
module top (input logic clk_i, input logic rst_ni);
    logic a_r, a_r1, a_ff, a_reg, a_next, a_n, a_d;
    logic [1:0] a_q;
    bus_if bus ();
    always_ff @(posedge clk_i) a_r <= a_next;
    always_ff @(posedge clk_i) a_r1 <= a_next;
    always_ff @(posedge clk_i) a_ff <= a_n;
    always_ff @(posedge clk_i) a_q <= a_d;
    always_ff @(posedge clk_i) if (!rst_ni) a_reg <= 0;
    always_ff @(posedge clk_i) bus.data_q <= bus.data_d;
endmodule
)");
    CHECK(result);
}

TEST_CASE("DFFName: Default suffixes are rejected") {
    CHECK("\n" + getDFFNameWarnings(R"(
module top (input logic clk_i);
    logic a_n, b_n, a_q, b_q, c_q, d_n, _q;
    always_ff @(posedge clk_i) a_n <= b_n;
    always_ff @(posedge clk_i) a_q <= b_q;
    always_ff @(posedge clk_i) c_q <= d_n;
    always_ff @(posedge clk_i) _q <= d_n;
endmodule
)") == R"(
4:32: 'a_n' should be a variable whose name ends with one of ["_reg", "_r", "_ff", "_q"]
5:39: 'b_q' should be a variable whose name ends with one of ["_next", "_n", "_d"]
6:32: 'c_q' has a different name before its suffix than its input 'd_n'
7:32: '_q' should be a variable whose name ends with one of ["_reg", "_r", "_ff", "_q"]
)");
}

TEST_CASE("DFFName: Pipeline stages are accepted") {
    auto result = runCheckTest("DFFName", R"(
module top (input logic clk_i);
    logic a_ff, a_ff2, a_ff39, a_ff40, b_ff1, b_ff2, c_q1, c_q2;
    always_ff @(posedge clk_i) a_ff2 <= a_ff;
    always_ff @(posedge clk_i) a_ff40 <= a_ff39;
    always_ff @(posedge clk_i) b_ff2 <= b_ff1;
    always_ff @(posedge clk_i) c_q2 <= #1 c_q1;
endmodule
)");
    CHECK(result);
}

TEST_CASE("DFFName: Pipeline stages are rejected") {
    CHECK("\n" + getDFFNameWarnings(R"(
module top (input logic clk_i);
    logic a_q, a_q0, a_q1, a_q2, a_q3, a_n;
    always_ff @(posedge clk_i) a_q1 <= a_q0;
    always_ff @(posedge clk_i) a_q2 <= a_q0;
    always_ff @(posedge clk_i) a_q3 <= a_q;
    always_ff @(posedge clk_i) a_q0 <= a_n;
endmodule
)") == R"(
4:40: 'a_q0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
5:40: 'a_q0' should be the previous pipeline stage 'a_q1'
6:40: 'a_q' should be the previous pipeline stage 'a_q2'
7:32: 'a_q0' should be a variable whose name ends with one of ["_reg", "_r", "_ff", "_q"]
)");
}

TEST_CASE("DFFName: Empty suffix lists disable their half of the check") {
    TidyConfig config;
    config.getCheckConfigs().dffOutputSuffix = {};
    config.getCheckConfigs().dffInputSuffix = {};

    auto code = R"(
module top (input logic clk_i);
    logic a, b, c_ff, d_n;
    always_ff @(posedge clk_i) a <= b;
    always_ff @(posedge clk_i) c_ff <= d_n;
endmodule
)";
    CHECK(runCheckTest("DFFName", code, config));

    config.getCheckConfigs().dffOutputSuffix = {"_ff"};
    CHECK("\n" + getDFFNameWarnings(code, config) == R"(
4:32: 'a' should be a variable whose name ends with one of ["_ff"]
)");
}

TEST_CASE("DFFName: Assignments that are not plain variable names are rejected") {
    CHECK("\n" + getDFFNameWarnings(R"(
`define A_q a_q
`define DEF_n b_n
`define ASSIGN(q, d) q <= d
module top (input logic clk_i);
    struct packed { logic a_q; logic b_n; } mystruct;
    logic a_q, b, b_n, d_ff, f_ff, j_ff, k_ff;
    logic [3:0] b_n4;
    always_ff @(posedge clk_i) `A_q <= b_n;
    always_ff @(posedge clk_i) mystruct.a_q <= b_n;
    always_ff @(posedge clk_i) d_ff <= mystruct.b_n;
    always_ff @(posedge clk_i) f_ff <= b_n4[2];
    always_ff @(posedge clk_i) j_ff <= `DEF_n;
    always_ff @(posedge clk_i) `ASSIGN(k_ff, b);
endmodule
)") == R"(
9:32: 'a_q' should be a variable whose name ends with one of ["_reg", "_r", "_ff", "_q"]
10:32: 'mystruct.a_q' should be a variable whose name ends with one of ["_reg", "_r", "_ff", "_q"]
11:40: 'mystruct.b_n' should be a variable whose name ends with one of ["_next", "_n", "_d"]
12:40: 'b_n4[2]' should be a variable whose name ends with one of ["_next", "_n", "_d"]
13:40: 'b_n' should be a variable whose name ends with one of ["_next", "_n", "_d"]
)");
}

TEST_CASE("DFFName: Flip-flop outputs driven outside always_ff are rejected") {
    CHECK("\n" + getDFFNameWarnings(R"(
module child (input logic in_q, output logic out_o);
    assign out_o = in_q;
endmodule
module top (input logic clk_i, input logic data_d);
    wire net_ff = 1;
    logic assign_ff, comb_ff, always_q, blocking_q, data_q, data_n;
    logic port_q, initial_q = 0, initial_d, other;
    always_comb comb_ff = 1;
    always @(posedge clk_i) always_q <= data_d;
    always_ff @(posedge clk_i) begin
        blocking_q = data_d;
        {data_n, other} = 2'b0;
    end
    always_ff @(posedge clk_i) initial_q <= initial_d;
    assign assign_ff = 1;
    child port_connection (.in_q(data_q), .out_o(port_q));
endmodule
)") == R"(
6:10: 'net_ff' has a flip-flop output suffix but is not driven by a nonblocking assignment inside always_ff
16:12: 'assign_ff' has a flip-flop output suffix but is not driven by a nonblocking assignment inside always_ff
9:17: 'comb_ff' has a flip-flop output suffix but is not driven by a nonblocking assignment inside always_ff
10:29: 'always_q' has a flip-flop output suffix but is not driven by a nonblocking assignment inside always_ff
12:9: 'blocking_q' has a flip-flop output suffix but is not driven by a nonblocking assignment inside always_ff
)");
}

TEST_CASE("DFFName: Increments inside always_ff are rejected") {
    CHECK("\n" + getDFFNameWarnings(R"(
module top (input logic clk_i);
    logic [3:0] count_q, down_q, other, mem_count, initial_count, neg_q, neg_d;
    always_ff @(posedge clk_i) begin
        count_q++;
        --down_q;
        other++;
        mem_count++;
        for (int i = 0; i < 4; i++) begin end
        neg_q <= -neg_d;
    end
    initial initial_count++;
endmodule
)") == R"(
5:9: 'count_q' is incremented or decremented inside always_ff; assign it with a nonblocking assignment instead
6:11: 'down_q' is incremented or decremented inside always_ff; assign it with a nonblocking assignment instead
7:9: 'other' is incremented or decremented inside always_ff; assign it with a nonblocking assignment instead
10:18: '-neg_d' should be a variable whose name ends with one of ["_next", "_n", "_d"]
)");
}

TEST_CASE("DFFName: Waive regex skips memories") {
    auto result = runCheckTest("DFFName", R"(
module top (input logic clk_i, input logic [1:0] addr);
    logic val;
    logic [3:0][3:0] mem2d, MEMORY;
    always_ff @(posedge clk_i) mem2d[addr] <= val;
    always_ff @(posedge clk_i) MEMORY[addr] <= val;
endmodule
)");
    CHECK(result);
}

TEST_CASE("DFFName: Waived if conditions skip their true branch") {
    auto code = R"(
module top (input logic clk_i, rst_ni, flush_i, reset);
    logic a_reg, b_reg, c_reg, d_reg, e_reg, g_reg;
    always_ff @(posedge clk_i) if (!rst_ni) a_reg <= 0;
    always_ff @(posedge clk_i) if ( flush_i ) b_reg <= 0;
    always_ff @(posedge clk_i) if (!rst_ni || flush_i) c_reg <= 0;
    always_ff @(posedge clk_i) if (flush_i||!rst_ni) d_reg <= 0;
    always_ff @(posedge clk_i) if (reset) e_reg <= 0;
    always_ff @(posedge clk_i) if (!rst_ni) g_reg <= 0; else g_reg <= 1;
endmodule
)";
    CHECK("\n" + getDFFNameWarnings(code) == R"(
8:52: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
9:71: '1' should be a variable whose name ends with one of ["_next", "_n", "_d"]
)");

    TidyConfig config;
    config.getCheckConfigs().dffWaiveIfConditions = {"flush_i||!rst_ni"};
    CHECK("\n" + getDFFNameWarnings(code, config) == R"(
4:54: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
5:56: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
6:65: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
8:52: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
9:54: '0' should be a variable whose name ends with one of ["_next", "_n", "_d"]
9:71: '1' should be a variable whose name ends with one of ["_next", "_n", "_d"]
)");
}
