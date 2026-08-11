// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyTest.h"

TEST_CASE("TypedefEnums: enum without typedef") {
    auto result = runCheckTest("TypedefEnums", R"(
module top;
    enum { IN, OUT } direction;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefEnums: enum in struct") {
    auto result = runCheckTest("TypedefEnums", R"(
module top;
    struct {
        enum { IN, OUT } direction;
    } colour_s;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefEnums: two enums") {
    auto result = runCheckTest("TypedefEnums", R"(
module top;
    typedef enum { RED, BLUE } first_enum;
    enum { A, B } second_enum;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefEnums: enum with typedef") {
    auto result = runCheckTest("TypedefEnums", R"(
module top;
    typedef enum { IN, OUT } direction_t;
    direction_t direction;
endmodule
)");
    CHECK(result);
}

TEST_CASE("TypedefEnums: forward declared enum") {
    auto result = runCheckTest("TypedefEnums", R"(
module top;
    typedef enum blah;
    typedef enum { A, B } blah;
endmodule
)");
    CHECK(result);
}
