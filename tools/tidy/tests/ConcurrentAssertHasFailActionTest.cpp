// SPDX-FileCopyrightText: Ajeetha Kumari Venkatesan
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("ConcurrentAssertHasFailAction: assert property without else fail action block") {
    auto result = runCheckTest("ConcurrentAssertHasFailAction", R"(
module top;
    bit clk, req, ack;

    a_req_ack: assert property (@(posedge clk) req |-> ##[1:3] ack);

endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("ConcurrentAssertHasFailAction: assert property with else fail action block") {
    auto result = runCheckTest("ConcurrentAssertHasFailAction", R"(
module top;
    bit clk, req, ack;

    a_req_ack: assert property (@(posedge clk) req |-> ##[1:3] ack)
        else $error("req=%0b ack=%0b", req, ack);

endmodule
)");
    CHECK(result);
}
