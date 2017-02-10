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

}
