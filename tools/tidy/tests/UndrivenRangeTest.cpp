// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"

TEST_CASE("Undriven range: simple case with a two bit bus") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module top;
  logic [1:0] a;
  always_comb
    a[0] = 1;
endmodule
)",
                               {}, &output);

    CHECK_FALSE(result);

    CHECK("\n" + output == R"(
source:3:15: warning: [SYNTHESIS-20] variable a has undriven bits: 1
  logic [1:0] a;
              ^
)");
}

TEST_CASE("Undriven range: a 32b bus with missing drivers") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module top;
  logic [31:0] a;
  always_comb begin
    a[7:0] = 8'hFF;
    a[11] = 1;
    a[30] = 0;
  end
endmodule
)",
                               {}, &output);

    CHECK_FALSE(result);

    CHECK("\n" + output == R"(
source:3:16: warning: [SYNTHESIS-20] variable a has undriven bits: 8:10, 12:29, 31
  logic [31:0] a;
               ^
)");
}

TEST_CASE("Undriven range: ignore fully undriven variables") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module top;
  logic [31:0] a;
endmodule
)",
                               {}, &output);
    CHECK(result);
}

TEST_CASE("Undriven range: AST must be traversed with VisitCanonical=true") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module foo(input logic i_data,
           output logic o_data);
  assign o_data = i_data;
endmodule

module top();
  logic data [2:0];
  assign data[0] = 1;
  foo foo0(.i_data(data[0]),
           .o_data(data[1]));

  foo foo1(.i_data(data[1]),
           .o_data(data[2]));
endmodule
)",
                               {}, &output);

    CHECK(result);
}

TEST_CASE("Undriven range: ensure variables with non-zero lower bounds are handled correctly") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
typedef logic [28:3] data_t;
module offset_bus(input data_t i_input,
                  output data_t o_output);
  assign o_output = i_input;
endmodule
    )",
                               {}, &output);
    CHECK(result);
}

TEST_CASE("Undriven range: ensure variables with non-zero lower bounds report the correct undriven "
          "bits") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
typedef logic [28:3] data_t;
module offset_bus(input data_t i_input,
                  output data_t o_output);
  assign o_output[28:4] = i_input;
endmodule
    )",
                               {}, &output);
    CHECK_FALSE(result);
    CHECK("\n" + output == R"(
source:4:33: warning: [SYNTHESIS-20] variable o_output has undriven bits: 3
                  output data_t o_output);
                                ^
)");
}

TEST_CASE("Undriven range: unpacked array driven through a range select") {
    auto result = runCheckTest("UndrivenRange", R"(
module top(input logic [7:0] a [3:0], output logic [7:0] o [3:0]);
  logic [7:0] d [3:0];
  assign d[3:1] = a[3:1];
  assign d[0] = '0;
  assign o = d;
endmodule
)");
    CHECK(result);
}

TEST_CASE("Undriven range: undriven last element of an unpacked array") {
    // Driver bounds are bit offsets over the whole array, so the undriven
    // element 0 of a [3:0] array is reported as its bit offsets
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module top(input logic [7:0] a [3:0], output logic [7:0] o [3:0]);
  logic [7:0] d [3:0];
  assign d[3:1] = a[3:1];
  assign o = d;
endmodule
)",
                               {}, &output);
    CHECK_FALSE(result);
    CHECK(output.find("variable d has undriven bits: 24:31") != std::string::npos);
}

TEST_CASE("Undriven range: undriven upper elements of a packed multidimensional array") {
    std::string output;
    auto result = runCheckTest("UndrivenRange", R"(
module top(input logic [15:0] a, output logic [3:0][7:0] o);
  logic [3:0][7:0] q;
  assign q[1:0] = a;
  assign o = q;
endmodule
)",
                               {}, &output);
    CHECK_FALSE(result);
    CHECK(output.find("variable q has undriven bits: 16:31") != std::string::npos);
}
