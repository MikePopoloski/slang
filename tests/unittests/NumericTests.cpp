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

    CHECK(exactlyEqual(SVInt("13'b1100xZ?01")[2], logic_t::z));
}

void checkRoundTrip(std::string str, LiteralBase base) {
    SVInt sv { string_view(str) };
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
    CHECK(SVInt("12'b101") == 5);
    CHECK(SVInt("12'b101") != 10);

    CHECK(SVInt("999'd37") < 39);
    CHECK(SVInt("100'd999999999999999999999999") <= SVInt("120'd999999999999999999999999"));
    CHECK(SVInt("100'sd99999999999999999999999999") >= SVInt("-120'sd999999999999977789999"));
    CHECK(SVInt("100'd99999999999999999999999999") < SVInt("-120'sd999999999999977789999"));
    CHECK(SVInt("100'd99999999999999999999999999") >= (uint64_t)-50);

    SVInt v(6, 0, false);
    v.setAllOnes();
    CHECK(v == SVInt("6'b111111"));
    v.setAllZeros();
    CHECK(v == 0);
    v.setAllX();
    CHECK(exactlyEqual(v, SVInt("6'bxxxxxx")));
    v.setAllZ();
    CHECK(exactlyEqual(v, SVInt("6'bzz??ZZ")));
}

TEST_CASE("Arithmetic", "[numeric]") {
    CHECK(SVInt("100'd99999999999") + SVInt("120'd987654321") == SVInt("137'd100987654320"));
    CHECK(SVInt("100'sd99999999999") + SVInt("-120'sd999987654321") == SVInt("-137'sd899987654322"));
    CHECK(SVInt("100'sd32") - SVInt(32) == 0);
    CHECK(SVInt("100'sd99999999999") * SVInt("-120'sd999987654321") == SVInt("-137'sd99998765431100012345679"));
    CHECK(SVInt("100'sd99999999999") / SVInt("-120'sd987654321") == SVInt(-101));
    CHECK(SVInt("100'sd99999999999") % SVInt("120'sd987654321") == SVInt(246913578));
    CHECK((SVInt(64, (uint64_t)-7, true) % SVInt(64, 3, true)) == (uint64_t)-1);

    SVInt v1("99'd99999999");
    SVInt v2 = v1++;
    CHECK(v2 == SVInt("99'd99999999"));
    CHECK(v1 == SVInt("99'd100000000"));

    --v1;
    CHECK(v2 == v1);

    CHECK(SVInt(64, 3, false).pow(SVInt(918245)) == SVInt("64'd12951281834385883507"));
}

TEST_CASE("Shifting", "[numeric]") {
    CHECK(SVInt("100'b11110000111").lshr(5) == 60);
    CHECK(exactlyEqual(SVInt("100'b11xxxZ00101").lshr(7), SVInt("20'b11xx")));
    CHECK(SVInt("64").shl(3) == 512);
    CHECK(exactlyEqual(SVInt("52'hffxx").shl(4), SVInt("52'hffxx0")));
}

TEST_CASE("Bitwise", "[numeric]") {
    CHECK(exactlyEqual(SVInt("100'b11xx1Z00x10") | SVInt("90'b10101xzx01z"), SVInt("90'b111x1xxxx1x")));
    CHECK(exactlyEqual(SVInt("100'b11xx1Z00x10") & SVInt("90'b10101xzx01z"), SVInt("90'b10x01x00010")));
    CHECK(exactlyEqual(SVInt("100'b11xx1Z00x10") ^ SVInt("90'b10101xzx01z"), SVInt("90'b01xx0xxxx0x")));
    CHECK(exactlyEqual(SVInt("11'b11xx1Z00x10").xnor(SVInt("11'b10101xzx01z")), SVInt("11'b10xx1xxxx1x")));
    CHECK(exactlyEqual(~SVInt("11'b11xx1Z00x10"), SVInt("12'b00xx0x11x01")));

    CHECK(SVInt("100'h1000000000000000").reductionOr() == logic_t(1));
    CHECK(SVInt("100'h10111111111111111111111111111111111").reductionAnd() == logic_t(0));
    CHECK(SVInt("35'b11111111111111111111111111111111111").reductionAnd() == logic_t(1));
    CHECK(SVInt("35'b11111100000011111111111111111101110").reductionXor() == logic_t(1));
}
