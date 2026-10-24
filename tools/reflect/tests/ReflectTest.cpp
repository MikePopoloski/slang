// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvTypeReflector.h"
#include "Test.h"
#include <catch2/matchers/catch_matchers_string.hpp>

using Catch::Matchers::ContainsSubstring;

static std::string reflect(std::string_view code) {
    auto tree = SyntaxTree::fromText(code);
    auto compilationPtr = std::make_unique<Compilation>();
    auto& compilation = *compilationPtr;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    SvTypeReflector reflector(std::move(compilationPtr), /* verbose */ false,
                              /* noSystemC */ false);
    reflector.reflect();
    return reflector.emit();
}

TEST_CASE("Reflect: only public declarations are emitted") {
    auto out = reflect(R"(
package p;
    typedef struct packed { logic a; } shown_t /* public */;
    typedef struct packed { logic a; } hidden_t;
    localparam int SHOWN /* public */ = 42;
    localparam int HIDDEN = 7;
endpackage
)");

    CHECK_THAT(out, ContainsSubstring("namespace p {"));
    CHECK_THAT(out, ContainsSubstring("struct shown_t {"));
    CHECK_THAT(out, ContainsSubstring("static constexpr std::uint32_t SHOWN = 42;"));
    CHECK_THAT(out, !ContainsSubstring("hidden_t"));
    CHECK_THAT(out, !ContainsSubstring("HIDDEN"));
}

TEST_CASE("Reflect: struct fields are mapped by width") {
    auto out = reflect(R"(
package p;
    typedef struct packed {
        logic        valid;
        logic [7:0]  id;
        logic [47:0] addr;
        logic [99:0] data;
    } req_t /* public */;
endpackage
)");

    CHECK_THAT(out, ContainsSubstring("bool valid"));
    CHECK_THAT(out, ContainsSubstring("std::uint32_t id"));
    CHECK_THAT(out, ContainsSubstring("std::uint64_t addr"));
    CHECK_THAT(out, ContainsSubstring("sc_dt::sc_bv<100> data"));
    CHECK_THAT(out, ContainsSubstring("static constexpr std::size_t _size = 157;"));
}

TEST_CASE("Reflect: scalar fields are value-initialized") {
    auto out = reflect(R"(
package p;
    typedef enum logic [1:0] { IDLE, BUSY } state_e /* public */;
    typedef struct packed { logic a; } inner_t /* public */;
    typedef struct packed {
        logic        flag;
        logic [31:0] count;
        logic [99:0] data;
        state_e      state;
        inner_t      inner;
    } outer_t /* public */;
endpackage
)");

    // Builtin types are otherwise left indeterminate by the defaulted constructor
    CHECK_THAT(out, ContainsSubstring("bool flag {};"));
    CHECK_THAT(out, ContainsSubstring("std::uint32_t count {};"));
    CHECK_THAT(out, ContainsSubstring("Type type {};"));

    // SystemC and generated types are initialized by their own constructors
    CHECK_THAT(out, ContainsSubstring("sc_dt::sc_bv<100> data;"));
    CHECK_THAT(out, ContainsSubstring("state_e state;"));
    CHECK_THAT(out, ContainsSubstring("inner_t inner;"));
}

TEST_CASE("Reflect: union storage") {
    auto out = reflect(R"(
package p;
    typedef union packed {
        logic [15:0]      half;
        logic [1:0][7:0]  bytes;
    } small_u /* public */;
    typedef union packed {
        logic [127:0]     wide;
        logic [1:0][63:0] dwords;
    } wide_u /* public */;
endpackage
)");

    CHECK_THAT(out, ContainsSubstring("std::uint32_t union_data {};"));
    CHECK_THAT(out, ContainsSubstring("sc_dt::sc_bv<128> union_data;"));
    CHECK_THAT(out, ContainsSubstring("half() const"));
    CHECK_THAT(out, ContainsSubstring("dwords() const"));
}

TEST_CASE("Reflect: enum values") {
    auto out = reflect(R"(
package p;
    typedef enum logic [2:0] { RED = 1, GREEN = 2, BLUE = 4 } color_e /* public */;
endpackage
)");

    CHECK_THAT(out, ContainsSubstring("struct color_e {"));
    CHECK_THAT(out, ContainsSubstring("enum Type : std::uint8_t {"));
    CHECK_THAT(out, ContainsSubstring("RED = 1"));
    CHECK_THAT(out, ContainsSubstring("GREEN = 2"));
    CHECK_THAT(out, ContainsSubstring("BLUE = 4"));
    CHECK_THAT(out, ContainsSubstring("static constexpr std::size_t _size = 3;"));
}

TEST_CASE("Reflect: inline enum fields") {
    auto out = reflect(R"(
package p;
    typedef struct packed {
        enum logic [1:0] { E0, E1 } marker;
        logic [3:0] a;
    } s_t /* public */;
    typedef union packed {
        enum logic [3:0] { F0, F1 } marker;
        logic [3:0] a;
    } u_t /* public */;
endpackage
)");

    // Anonymous enum types are mapped by width
    CHECK_THAT(out, ContainsSubstring("std::uint32_t marker {};"));
    CHECK_THAT(out, ContainsSubstring("static constexpr std::size_t marker_w = 2;"));
    CHECK_THAT(out, ContainsSubstring("marker() const"));
    CHECK_THAT(out, ContainsSubstring("a() const"));
    CHECK_THAT(out, !ContainsSubstring("#include \".h\""));
}

TEST_CASE("Reflect: union member types are qualified only when needed") {
    auto out = reflect(R"(
package q;
    typedef struct packed { logic [1:0] x; logic [1:0] y; } inner_t /* public */;
endpackage
package p;
    typedef union packed { q::inner_t i; logic [3:0] a; } u_t /* public */;
endpackage
)");

    CHECK_THAT(out, ContainsSubstring("q::inner_t i() const"));
    CHECK_THAT(out, ContainsSubstring("operator q::inner_t() const"));
    CHECK_THAT(out, ContainsSubstring("static_cast<q::inner_t>(*this)"));
    CHECK_THAT(out, ContainsSubstring("\n        std::uint32_t a() const"));
    CHECK_THAT(out, ContainsSubstring("static_cast<std::uint32_t>(*this)"));
    CHECK_THAT(out, !ContainsSubstring("::std::uint32_t"));
    CHECK_THAT(out, !ContainsSubstring("static_cast<::>"));
}
