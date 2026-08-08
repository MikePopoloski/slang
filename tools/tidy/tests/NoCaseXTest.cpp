// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("NoCaseX: Use of casex") {
    auto result = runCheckTest("NoCaseX", R"(
module top;
    bit a, b;

    always_comb begin
        casex (a)
            1'b1: b = 1'b1;
            default: b = 1'bx;
        endcase
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoCaseX: Use of casex in pattern case statement") {
    auto result = runCheckTest("NoCaseX", R"(
module top;
    bit a, b;

    always_comb begin
        casex (a) matches
            1'b?: b = 1'b1;
            default: b = 1'bx;
        endcase
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoCaseX: Nested casex inside case") {
    auto result = runCheckTest("NoCaseX", R"(
module top;
    bit a, b, c;

    always_comb begin
        case (a)
            1'b1: casex (b)
                1'b1: c = 1'b1;
                default: c = 1'bx;
            endcase
            default: c = 1'b0;
        endcase
    end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoCaseX: Use of case and casez") {
    auto result = runCheckTest("NoCaseX", R"(
module top;
    bit a, b;

    always_comb begin
        casez (a)
            1'b1: b = 1'b1;
            default: b = 1'bx;
        endcase

        case (a)
            1'b1: b = 1'b1;
            default: b = 1'bx;
        endcase
    end
endmodule
)");
    CHECK(result);
}
