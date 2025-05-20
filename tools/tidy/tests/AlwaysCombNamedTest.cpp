// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("AlwaysCombBlockNamed: Unnamed always_comb block") {
    auto result = runCheckTest("AlwaysCombBlockNamed", R"(
module top ();
    logic a, b;
    always_comb begin
        a = b;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysCombBlockNamed: Named always_comb block") {
    auto result = runCheckTest("AlwaysCombBlockNamed", R"(
module top ();
    logic a, b;
    always_comb begin : named_comb2
        a = b;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("AlwaysCombBlockNamed: Unnamed simple always_comb block") {
    auto result = runCheckTest("AlwaysCombBlockNamed", R"(
module add_or_sub
    #(parameter N = 4)
    (
        input logic [N-1:0] x_i, y_i,
        input logic add,
        output logic [N-1:0] z_o
    );

    always_comb
        if (add)
            z = x + y;
        else
            z = x - y;
endmodule
)");
    CHECK(result);
}
