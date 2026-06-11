// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("NoLatchesOnDesign: Design with latch") {
    auto result = runCheckTest("NoLatchesOnDesign", R"(
module top (
    input logic a,
    output logic b
);
    always_latch begin
        b <= a;
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoLatchesOnDesign: Design without latch") {
    auto result = runCheckTest("NoLatchesOnDesign", R"(
module top (
    input logic a,
    output logic b
);
    always_comb begin
        b = a;
    end
endmodule
)");
    CHECK(result);
}
