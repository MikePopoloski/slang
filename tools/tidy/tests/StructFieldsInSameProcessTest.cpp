// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"

TEST_CASE("StructFieldsInSameProcess: Fields split across two always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    always_comb begin
        data.a = 1'b0;
    end

    always_comb begin
        data.b = 1'b1;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("StructFieldsInSameProcess: Fields split across three always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
        logic c;
    } data_t;

    data_t data;

    always_comb data.a = 1'b0;
    always_comb data.b = 1'b1;
    always_comb data.c = 1'b0;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("StructFieldsInSameProcess: Continuous assignment mixed with always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    assign data.a = 1'b0;

    always_comb begin
        data.b = 1'b1;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("StructFieldsInSameProcess: All fields in the same always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    always_comb begin
        data.a = 1'b0;
        data.b = 1'b1;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: All fields assigned continuously") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    assign data.a = 1'b0;
    assign data.b = 1'b1;
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: Whole struct assigned in a single always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    always_comb begin
        data = '0;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: Different structs driven by their own always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t first;
    data_t second;

    always_comb begin
        first.a = 1'b0;
        first.b = 1'b1;
    end

    always_comb begin
        second.a = 1'b0;
        second.b = 1'b1;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: always_ff drivers are out of scope") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top (input logic clk_i);
    typedef struct packed {
        logic a;
        logic b;
    } data_t;

    data_t data;

    always_ff @(posedge clk_i) begin
        data.a <= 1'b0;
    end

    always_comb begin
        data.b = 1'b1;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: Unpacked struct fields split across two always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct {
        logic a;
        logic b;
    } data_t;

    data_t data;

    always_comb begin
        data.a = 1'b0;
    end

    always_comb begin
        data.b = 1'b1;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("StructFieldsInSameProcess: Non struct variable split across two always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    logic [3:0] data;

    always_comb begin
        data[1:0] = 2'b00;
    end

    always_comb begin
        data[3:2] = 2'b11;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: Struct output port driven by a single always_comb") {
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
package pkg;
    typedef struct packed {
        logic a;
        logic b;
    } data_t;
endpackage

module child (output pkg::data_t data_o);
    always_comb begin
        data_o.a = 1'b0;
        data_o.b = 1'b1;
    end
endmodule

module top;
    pkg::data_t data;
    child i_child (.data_o(data));
endmodule
)");
    CHECK(result);
}

TEST_CASE("StructFieldsInSameProcess: Diagnostic points at the second process") {
    std::string output;
    auto result = runCheckTest("StructFieldsInSameProcess", R"(
module top;
    typedef struct packed {
        logic a;
        logic b;
        logic c;
    } data_t;

    data_t data;

    always_comb data.a = 1'b0;

    always_comb begin
        data.b = 1'b1;
        data.c = 1'b0;
    end
endmodule
)",
                               {}, &output);

    CHECK_FALSE(result);

    CHECK("\n" + output == R"(
source:14:9: warning: [SYNTHESIS-33] fields of struct 'data' are driven from more than one process; drive all of them from the same always_comb or use only continuous assignments
        data.b = 1'b1;
        ^~~~~~
)");
}
