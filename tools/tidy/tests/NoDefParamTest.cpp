// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("NoDefParam: use of defparam") {
    auto result = runCheckTest("NoDefParam", R"(
module child #(parameter int WIDTH = 8);
endmodule

module top;
    child c();
    defparam c.WIDTH = 16;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("NoDefParam: parameter override without defparam") {
    auto result = runCheckTest("NoDefParam", R"(
module child #(parameter int WIDTH = 8);
endmodule

module top;
    child #(.WIDTH(16)) c();
endmodule
)");
    CHECK(result);
}
