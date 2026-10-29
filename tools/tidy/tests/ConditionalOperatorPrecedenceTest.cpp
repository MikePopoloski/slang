// SPDX-FileCopyrightText: Ajeetha Kumari Venkatesan
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("ConditionalOperatorPrecedence: equality and conditional mixed without parentheses") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [3:0] data;
    bit sel;

    constraint c_data { data == sel ? 4'h5 : 4'h6; }

endclass
)");
    CHECK_FALSE(result);
}

TEST_CASE("ConditionalOperatorPrecedence: inequality and conditional mixed without parentheses") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [3:0] data;
    bit sel;

    constraint c_data { data != sel ? 4'h5 : 4'h6; }

endclass
)");
    CHECK_FALSE(result);
}

TEST_CASE("ConditionalOperatorPrecedence: relational and conditional mixed without parentheses") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [7:0] len;
    bit [7:0] lim;

    constraint c_len { len < lim ? 8'd4 : 8'd8; }

endclass
)");
    CHECK_FALSE(result);
}

TEST_CASE("ConditionalOperatorPrecedence: conditional explicitly parenthesised") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [3:0] data;
    bit sel;

    constraint c_data { data == (sel ? 4'h5 : 4'h6); }

endclass
)");
    CHECK(result);
}

TEST_CASE("ConditionalOperatorPrecedence: comparison explicitly parenthesised") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [3:0] data;
    bit sel;

    constraint c_data { (data == sel) ? 4'h5 : 4'h6; }

endclass
)");
    CHECK(result);
}

TEST_CASE("ConditionalOperatorPrecedence: boolean branches are an intended conditional") {
    auto result = runCheckTest("ConditionalOperatorPrecedence", R"(
class pkt_c;
    rand bit [7:0] len;
    bit [1:0] mode;

    constraint c_len { mode == 1 ? len < 10 : len > 20; }

endclass
)");
    CHECK(result);
}
