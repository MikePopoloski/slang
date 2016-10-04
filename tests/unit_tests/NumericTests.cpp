#include "Catch/catch.hpp"
#include "slang.h"
#include "SVInt.h"

using namespace slang;

namespace {

TEST_CASE("Construction", "[numeric]") {
    SVInt value1;
    SVInt value2 = 924;
    SVInt value3(924, false);
    SVInt value4(61, 924, false);

    CHECK(value1 == 0);
    CHECK(value2 != value1);
    CHECK(value2 == value3);
    CHECK(value4 == value3);
}

TEST_CASE("Equality", "[numeric]") {
    SVInt a = logic_t::x;

    CHECK(SVInt(9000) == SVInt(1024, 9000, false));
    CHECK(SVInt(-4) == -4);
    CHECK(SVInt(-4) != SVInt(9999, -4, true));
    CHECK(SVInt(-4, true) == SVInt(9999, -4, true));
}

}