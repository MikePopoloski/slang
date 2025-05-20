// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("AlwaysCombNonBlocking: Non blocking assignment inside always_comb") {
    auto result = runCheckTest("AlwaysCombNonBlocking", R"(
module top ();
    logic a, b;
    always_comb begin
        a <= b;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysCombNonBlocking: Blocking assignment inside always_comb") {
    auto result = runCheckTest("AlwaysCombNonBlocking", R"(
module top ();
    logic a, b;
    always_comb begin
        a = b;
    end
endmodule
)");
    CHECK(result);
}
