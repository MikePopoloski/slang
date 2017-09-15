#include "Test.h"

#include "numeric/SVInt.h"

TEST_CASE("Construction", "[numeric]") {
    SVInt value1;
    SVInt value2(924);
    SVInt value3(924, false);
    SVInt value4(61, 924, false);
    SVInt value5(69, (uint64_t)-924, true);

    CHECK(value1 == 0);
    CHECK(value2 != value1);
    CHECK(value2 == value3);
    CHECK(value4 == value3);

    CHECK(value5.isNegative());
    value5.setSigned(false);
    CHECK(value5.isNegative());

    CHECK(exactlyEqual("13'b1100xZ?01"_si[2], logic_t::z));

    CHECK_THROWS(""_si);
    CHECK_THROWS("'"_si);
    CHECK_THROWS("0'd3"_si);
    CHECK_THROWS("-"_si);
    CHECK_THROWS("+"_si);
    CHECK_THROWS("z'd3"_si);
    CHECK_THROWS("1's"_si);
    CHECK_THROWS("1'f"_si);
    CHECK_THROWS("asdf"_si);
    CHECK_THROWS("3'b8"_si);
}

void checkRoundTrip(string str, LiteralBase base) {
    SVInt sv = SVInt::fromString(string_view(str));
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
    CHECK(exactlyEqual(v, "6'bxxxxxx"_si));
    v.setAllZ();
    CHECK(exactlyEqual(v, "6'bzz??ZZ"_si));
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
    CHECK(exactlyEqual("100'b11xxxZ00101"_si.lshr(7), "20'b11xx"_si));
    CHECK("64"_si.shl(3) == 512);
    CHECK(exactlyEqual("52'hffxx"_si.shl(4), "52'hffxx0"_si));
}

TEST_CASE("Bitwise", "[numeric]") {
    CHECK(exactlyEqual("100'b11xx1Z00x10"_si | "90'b10101xzx01z"_si, "90'b111x1xxxx1x"_si));
    CHECK(exactlyEqual("100'b11xx1Z00x10"_si & "90'b10101xzx01z"_si, "90'b10x01x00010"_si));
    CHECK(exactlyEqual("100'b11xx1Z00x10"_si ^ "90'b10101xzx01z"_si, "90'b01xx0xxxx0x"_si));
    CHECK(exactlyEqual("11'b11xx1Z00x10"_si.xnor("11'b10101xzx01z"_si), "11'b10xx1xxxx1x"_si));
    CHECK(exactlyEqual(~"11'b11xx1Z00x10"_si, "12'b00xx0x11x01"_si));

    CHECK("100'h1000000000000000"_si.reductionOr() == logic_t(1));
    CHECK("100'h10111111111111111111111111111111111"_si.reductionAnd() == logic_t(0));
    CHECK("35'b11111111111111111111111111111111111"_si.reductionAnd() == logic_t(1));
    CHECK("35'b11111100000011111111111111111101110"_si.reductionXor() == logic_t(1));
}
