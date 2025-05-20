// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("XilinxDoNotCareValues: Use of 'd") {
    auto result = runCheckTest("XilinxDoNotCareValues", R"(
module top;
    logic [3:0] a = 4'd?;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("XilinxDoNotCareValues: Use of 'b") {
    auto result = runCheckTest("XilinxDoNotCareValues", R"(
module top;
    logic [3:0] a = 4'b?;
endmodule
)");
    CHECK(result);
}

TEST_CASE("XilinxDoNotCareValues: No do-not-care values") {
    auto result = runCheckTest("XilinxDoNotCareValues", R"(
module top;
    logic [3:0] a = 4'd10;
endmodule
)");
    CHECK(result);
}

TEST_CASE("XilinxDoNotCareValues: No do-not-care values but with comment") {
    auto result = runCheckTest("XilinxDoNotCareValues", R"(
module top;
    logic [3:0] a =
       /*'d?*/4'd10;
endmodule
)");
    CHECK(result);
}
