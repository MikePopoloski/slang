#include "Test.h"

#include "numeric/SVInt.h"

TEST_CASE("Construction", "[numeric]") {
    SVInt value1;
    SVInt value2(924);
    SVInt value3(924, false);
    SVInt value4(61, 924, false);
    SVInt value5(69, (uint64_t)-924, true);
    SVInt value6(-924);
    SVInt value7(63, UINT64_MAX, false);

    CHECK(value1 == 0);
    CHECK(value2 != value1);
    CHECK(value2 == value3);
    CHECK(value4 == value3);
    CHECK(value6 == -924);
    CHECK(value7 == "63'hffffffffffffffff"_si);
    CHECK(SVInt(0, true) == 0);
    CHECK(SVInt(UINT64_MAX, true) == UINT64_MAX);

    CHECK(value5.isNegative());
    value5.setSigned(false);
    CHECK(value5.isNegative());
    value5.setSigned(true);

    CHECK(value2.isEven());
    CHECK(value7.isOdd());
    CHECK(value5.getBitWidth() == 69);
    CHECK(value5.getActiveBits() == 69);
    CHECK(value5.getMinRepresentedBits() == 11);
    CHECK(value7.getMinRepresentedBits() == 63);
    CHECK(SVInt(1000, 2, true).getActiveBits() == 2);
    CHECK(SVInt(1000, 2, true).getMinRepresentedBits() == 3);

    value1 = value2;
    CHECK(value1 == value2);

    CHECK(value6.as<uint8_t>() == nullopt);
    CHECK(value6.as<uint16_t>() == uint16_t(-924));
    CHECK(value6.as<int16_t>() == -924);
    CHECK(value7.as<uint64_t>() == 9223372036854775807ULL);

    value5.setAllOnes();
    CHECK(value5 == "69'hffffffffffffffffff"_si);
    value5.setAllX();
    CHECK_THAT(value5, exactlyEquals("69'hx"_si));
    value5.setAllZ();
    CHECK_THAT(value5, exactlyEquals("69'hz"_si));
    value5.setAllZeros();
    CHECK(value5 == 0);
    CHECK(value5.getBitWidth() == 69);

    value1 = std::move(value1);
    value1 = value5;
    CHECK(value1 == value5);

    CHECK_THAT("13'b1100xZ?01"_si[2], exactlyEquals(logic_t::z));

    // extra digits should truncate from the left
    CHECK("4'hxxffa"_si == 10);

    // X and Z leading digits get extended out to the width of the integer
    CHECK_THAT("100'hx10"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("100'bx10"_si[1], exactlyEquals(logic_t(1)));

    // Make sure to check unknown extension with multiple of 64-bit words also.
    CHECK_THAT("128'hx10"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("128'bx10"_si[1], exactlyEquals(logic_t(1)));

    CHECK_THROWS(""_si);
    CHECK_THROWS("'"_si);
    CHECK_THROWS("30'"_si);
    CHECK_THROWS("0'd3"_si);
    CHECK_THROWS("-"_si);
    CHECK_THROWS("+"_si);
    CHECK_THROWS("z'd3"_si);
    CHECK_THROWS("1's"_si);
    CHECK_THROWS("1'f"_si);
    CHECK_THROWS("1'sb"_si);
    CHECK_THROWS("asdf"_si);
    CHECK_THROWS("3'b8"_si);
    CHECK_THROWS("3'dxxx"_si);
    CHECK_THROWS("3'df"_si);
    CHECK_THROWS("3'of"_si);
}

TEST_CASE("logic_t operators", "[numeric]") {
    logic_t v1(1);
    logic_t v2(0);

    CHECK(v1 == logic_t(1));
    CHECK(v2 != logic_t(1));
    CHECK((v1 | v2) == logic_t(1));
    CHECK((v1 & v2) == logic_t(0));
    CHECK((v1 ^ v2) == logic_t(1));
    CHECK((v1 && v2) == logic_t(0));
    CHECK((v1 || v2) == logic_t(1));
    CHECK(v1);
    CHECK(!v2);
    CHECK(~v2);
    CHECK(!v1.isUnknown());
    CHECK(!v2.isUnknown());
    CHECK(logic_t::x.isUnknown());
    CHECK(logic_t::z.isUnknown());
    CHECK(!bool(logic_t::x));
    CHECK(!bool(logic_t::z));

    CHECK_THAT(v1 == logic_t::x, exactlyEquals(logic_t::x));
    CHECK_THAT(v1 != logic_t::z, exactlyEquals(logic_t::x));
    CHECK_THAT(v1 & logic_t::z, exactlyEquals(logic_t::x));
    CHECK_THAT(v1 ^ logic_t::z, exactlyEquals(logic_t::x));
    CHECK_THAT(v1 | logic_t::z, exactlyEquals(logic_t(1)));
    CHECK_THAT(v1 || logic_t::z, exactlyEquals(logic_t(1)));
    CHECK_THAT(logic_t::x || v1, exactlyEquals(logic_t(1)));
    CHECK_THAT(logic_t::x || logic_t::z, exactlyEquals(logic_t::x));
    CHECK_THAT(v1 && logic_t::z, exactlyEquals(logic_t::x));
    CHECK_THAT(v2 && logic_t::z, exactlyEquals(logic_t(0)));
}

void checkRoundTrip(string str, LiteralBase base) {
    SVInt sv = SVInt::fromString(string_view(str));
    str.erase(std::remove(str.begin(), str.end(), '_'), str.end());
    CHECK(sv.toString(base) == str);
}

TEST_CASE("SVInt to string (and back)", "[numeric]") {
    checkRoundTrip("22'd10", LiteralBase::Decimal);
    checkRoundTrip("92'so10_0214_562", LiteralBase::Octal);
    checkRoundTrip("-5'sd10", LiteralBase::Decimal);
    checkRoundTrip("-993'shff", LiteralBase::Hex);
    checkRoundTrip("12'b101010101", LiteralBase::Binary);
    checkRoundTrip("12'dx", LiteralBase::Decimal);
    checkRoundTrip("12'dz", LiteralBase::Decimal);
    checkRoundTrip("32", LiteralBase::Decimal);
    checkRoundTrip("-999989", LiteralBase::Decimal);
    checkRoundTrip("12'b101x101z1", LiteralBase::Binary);

    std::ostringstream ss;
    ss << "96'd192834"_si;
    CHECK(ss.str() == "96'h2f142");
    CHECK(ss.str() == "96'd192834"_si.toString());
    CHECK("96'd192834"_si.toString(LiteralBase::Decimal) == "96'd192834");
    CHECK("96'd192834"_si.toString(LiteralBase::Octal) == "96'o570502");
    CHECK("96'd192834"_si.toString(LiteralBase::Binary) == "96'b101111000101000010");

    CHECK("1'dz"_si.toString(LiteralBase::Decimal) == "1'dz");
    CHECK(SVInt(32, 0, true).toString() == "0");
}

TEST_CASE("Comparison", "[numeric]") {
    CHECK(SVInt(9000) == SVInt(1024, 9000, false));
    CHECK(SVInt(-4) == (uint64_t)-4);
    CHECK(SVInt((uint64_t)-4, false) != SVInt(9999, (uint64_t)-4, true));
    CHECK(SVInt(-4) == SVInt(9999, (uint64_t)-4, true));
    CHECK("12'b101"_si == 5);
    CHECK("12'b101"_si != 10);

    CHECK("999'd37"_si < 39);
    CHECK("100'd999999999999999999999999"_si <= "120'd999999999999999999999999"_si);
    CHECK("100'sd99999999999999999999999999"_si >= "-120'sd999999999999977789999"_si);
    CHECK("100'd99999999999999999999999999"_si < "-120'sd999999999999977789999"_si);
    CHECK("100'd99999999999999999999999999"_si >= (uint64_t)-50);

    SVInt v(6, 0, false);
    v.setAllOnes();
    CHECK(v == "6'b111111"_si);
    v.setAllZeros();
    CHECK(v == 0);
    v.setAllX();
    CHECK_THAT(v, exactlyEquals("6'bxxxxxx"_si));
    v.setAllZ();
    CHECK_THAT(v, exactlyEquals("6'bzz??ZZ"_si));
}

TEST_CASE("Arithmetic", "[numeric]") {
    CHECK("100'd99999999999"_si + "120'd987654321"_si == "137'd100987654320"_si);
    CHECK("100'sd99999999999"_si + "-120'sd999987654321"_si == "-137'sd899987654322"_si);
    CHECK("100'sd32"_si - SVInt(32) == 0);
    CHECK("100'sd99999999999"_si * "-120'sd999987654321"_si == "-137'sd99998765431100012345679"_si);
    CHECK("100'sd99999999999"_si / "-120'sd987654321"_si == SVInt(-101));
    CHECK("100'sd99999999999"_si % "120'sd987654321"_si == SVInt(246913578));
    CHECK((SVInt(64, (uint64_t)-7, true) % SVInt(64, 3, true)) == (uint64_t)-1);

    SVInt v1 = "99'd99999999"_si;
    SVInt v2 = v1++;
    CHECK(v2 == "99'd99999999"_si);
    CHECK(v1 == "99'd100000000"_si);

    --v1;
    CHECK(v2 == v1);

    CHECK(SVInt(64, 3, false).pow(SVInt(918245)) == "64'd12951281834385883507"_si);
}

TEST_CASE("Shifting", "[numeric]") {
    CHECK("100'b11110000111"_si.lshr(5) == 60);
    CHECK_THAT("100'b11xxxZ00101"_si.lshr(7), exactlyEquals("20'b11xx"_si));
    CHECK("64"_si.shl(3) == 512);
    CHECK_THAT("52'hffxx"_si.shl(4), exactlyEquals("52'hffxx0"_si));
}

TEST_CASE("Bitwise", "[numeric]") {
    CHECK_THAT("100'b11xx1Z00x10"_si | "90'b10101xzx01z"_si, exactlyEquals("90'b111x1xxxx1x"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si & "90'b10101xzx01z"_si, exactlyEquals("90'b10x01x00010"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si ^ "90'b10101xzx01z"_si, exactlyEquals("90'b01xx0xxxx0x"_si));
    CHECK_THAT("11'b11xx1Z00x10"_si.xnor("11'b10101xzx01z"_si), exactlyEquals("11'b10xx1xxxx1x"_si));
    CHECK_THAT(~"11'b11xx1Z00x10"_si, exactlyEquals("12'b00xx0x11x01"_si));

    CHECK("100'h1000000000000000"_si.reductionOr() == logic_t(1));
    CHECK("100'h10111111111111111111111111111111111"_si.reductionAnd() == logic_t(0));
    CHECK("35'b11111111111111111111111111111111111"_si.reductionAnd() == logic_t(1));
    CHECK("35'b11111100000011111111111111111101110"_si.reductionXor() == logic_t(1));
}
