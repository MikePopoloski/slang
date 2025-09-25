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
