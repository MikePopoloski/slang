// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("EnforceModuleInstantiationPrefix: Incorrect module instantiation prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module test ();
endmodule

module top();
    test test();
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforceModuleInstantiationPrefix: Correct module instantiation prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module test ();
endmodule

module top();
    test i_test();
endmodule
)");
    CHECK(result);
}
