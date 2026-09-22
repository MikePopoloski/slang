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

TEST_CASE("EnforceModuleInstantiationPrefix: Incorrect submodule instantiation prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module subtest ();
endmodule

module test ();
    subtest subtest();
endmodule

module top();
    test i_test();
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforceModuleInstantiationPrefix: Correct submodule instantiation prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module subtest ();
endmodule

module test ();
    subtest i_subtest();
endmodule

module top();
    test i_test();
endmodule
)");
    CHECK(result);
}

TEST_CASE("EnforceModuleInstantiationPrefix: Incorrect instance array prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module test ();
endmodule

module top();
    test test[1:0]();
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("EnforceModuleInstantiationPrefix: Correct instance array prefix") {
    auto result = runCheckTest("EnforceModuleInstantiationPrefix", R"(
module test ();
endmodule

module top();
    test i_test[1:0]();
endmodule
)");
    CHECK(result);
}
