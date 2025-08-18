// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("OnlyANSIPortDecl: Use of non-ANSI port declaration style") {
    auto result = runCheckTest("OnlyANSIPortDecl", R"(
module top(a,b,c);
    input logic a;
    inout logic b;
    output logic c;

endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("OnlyANSIPortDecl: Use of ANSI port declaration style") {
    auto result = runCheckTest("OnlyANSIPortDecl", R"(
module top(
    input logic a,
    inout logic b,
    output logic c,
);

endmodule
)");
    CHECK(result);
}

TEST_CASE("OnlyANSIPortDecl: No port declaration") {
    auto result = runCheckTest("OnlyANSIPortDecl", R"(
module top;
endmodule
)");
    CHECK(result);
}
