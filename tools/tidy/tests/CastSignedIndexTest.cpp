// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("CastSignedIndex: Negative index") {
    auto result = runCheckTest("CastSignedIndex", R"(
module top;
    logic a [4];

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            a[2'(i)] = i;
        end
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("CastSignedIndex: Signed index") {
    auto result = runCheckTest("CastSignedIndex", R"(
module top;
    logic a [4];

    always_comb begin
        for (int i = 0; i < 4; i++) begin
            a[i] = i;
        end
    end
endmodule
)");
    CHECK(result);
}
