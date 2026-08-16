// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyConfigParser.h"
#include "TidyTest.h"

TEST_CASE("TypedefStructUnion: struct without typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    struct {
        bit a;
    } a_s;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: packed struct without typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    struct packed {
        bit a;
    } a_s;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: union without typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    union {
        bit a;
    } a_u;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: tagged union without typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    union tagged {
        bit a;
    } a_u;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: struct with typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef struct {
        bit a;
    } a_s;
    typedef struct packed {
        bit a;
    } b_s;
endmodule
)");
    CHECK(result);
}

TEST_CASE("TypedefStructUnion: union with typedef") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef union {
        bit a;
    } a_u;
    typedef union tagged {
        bit a;
    } b_u;
endmodule
)");
    CHECK(result);
}

TEST_CASE("TypedefStructUnion: allow nested anon struct") {
    auto config_str = std::string(R"(CheckConfigs:
    allowNestedAnon: true)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef struct {
        bit a;
        struct {
            logic c;
        } b;
    } abc_s;
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("TypedefStructUnion: deny nested anon struct") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef struct {
        bit a;
        struct {
            logic c;
        } b;
    } abc_s;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: allow nested anon union") {
    auto config_str = std::string(R"(CheckConfigs:
    allowNestedAnon: true)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef struct {
        bit a;
        union {
            logic c;
        } b;
    } abc_s;
endmodule
)",
                               config);
    CHECK(result);
}

TEST_CASE("TypedefStructUnion: deny nested anon union") {
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    typedef struct {
        bit a;
        union {
            logic c;
        } b;
    } abc_s;
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("TypedefStructUnion: nested struct errors") {
    std::string output;
    auto result = runCheckTest("TypedefStructUnion", R"(
module top;
    struct {
        struct { logic a; } b;
    } ab_s;
endmodule
)",
                               {}, &output);
    CHECK_FALSE(result);
    CHECK("\n" + output == R"(
source:3:5: warning: [STYLE-25] struct/union declaration should be named using a typedef
    struct {
    ^
source:4:9: warning: [STYLE-25] struct/union declaration should be named using a typedef
        struct { logic a; } b;
        ^
)");
}
