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

void checkRoundTrip(std::string str, LiteralBase base) {
	SVInt sv(str);
	str.erase(std::remove(str.begin(), str.end(), '_'), str.end());
	CHECK(sv.toString(base) == str);
}

TEST_CASE("String round trip", "[numeric]") {
	checkRoundTrip("22'd10", LiteralBase::Decimal);
	checkRoundTrip("92'so10_0214_562", LiteralBase::Octal);
	checkRoundTrip("-5'sd10", LiteralBase::Decimal);
	checkRoundTrip("-993'shff", LiteralBase::Hex);
	checkRoundTrip("12'b101010101", LiteralBase::Binary);
	checkRoundTrip("12'dx", LiteralBase::Decimal);
	checkRoundTrip("32", LiteralBase::Decimal);
	checkRoundTrip("-999989", LiteralBase::Decimal);
	checkRoundTrip("12'b101x101z1", LiteralBase::Binary);
}

TEST_CASE("Equality", "[numeric]") {
    SVInt a = logic_t::x;

    CHECK(SVInt(9000) == SVInt(1024, 9000, false));
    CHECK(SVInt(-4) == -4);
    CHECK(SVInt(-4) != SVInt(9999, -4, true));
    CHECK(SVInt(-4, true) == SVInt(9999, -4, true));
}

}