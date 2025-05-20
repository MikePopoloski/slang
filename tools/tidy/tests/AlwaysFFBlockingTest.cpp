// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("AlwaysFFBlocking: Blocking assignment inside always_ff") {
    auto result = runCheckTest("AlwaysFFBlocking", R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
        a = b;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("AlwaysFFBlocking: Correct blocking assignment inside always_ff") {
    auto result = runCheckTest("AlwaysFFBlocking", R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
        int k = 1;
        k = 42;
        a <= b;
    end
endmodule
)");
    CHECK(result);
}

TEST_CASE("AlwaysFFBlocking: Incorrect blocking assignment inside always_ff") {
    auto result = runCheckTest("AlwaysFFBlocking", R"(
module top ();
    logic a, b, c;
    always_ff @(posedge c) begin
        int k = 1;
        k = 42;
        a = b;
    end
endmodule
)");
    CHECK_FALSE(result);
}
