#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

TEST_CASE("Simple eval", "[eval") {
    ScriptSession session;
    auto value = session.eval("3 * 3");
    CHECK(value.integer() == 9);

    session.eval("int i = 4;");
    value = session.eval("i + 9");
    CHECK(value.integer() == 13);
}

TEST_CASE("Function call", "[eval]") {
    ScriptSession session;
    session.eval("function logic [15:0] foo(int a, int b); return a + b; endfunction");

    auto value = session.eval("foo(3, 4)");
    CHECK(value.integer() == 7);
}

}
