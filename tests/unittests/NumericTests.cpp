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
    CHECK(SVInt(UINT64_MAX, true) == -1);

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
    value5 = value5;
    CHECK(value5 == value5);

    CHECK(value6.as<uint8_t>() == std::nullopt);
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

    SVInt value8 = SVInt::createFillX(878, false);
    value8.setAllOnes();
    CHECK_THAT(value8[877], exactlyEquals(logic_t(1)));
    value8.setAllZ();
    CHECK_THAT(value8[877], exactlyEquals(logic_t::z));

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wself-move"
#endif
    value1 = std::move(value1);
#ifdef __clang__
#pragma clang diagnostic pop
#endif

    value1 = value5;
    CHECK(value1 == value5);

    // Check copy assignment.
    SVInt value9 = "124'd123"_si;
    SVInt two(2);
    value9 = two;
    CHECK(value9 == 2);

    SVInt value10 = "124'd123"_si;
    value9 = value10;
    CHECK(value9 == 123);
    SVInt value11 = "10'sbzxzxzz"_si;
    value9 = value11;
    CHECK_THAT(value9, exactlyEquals(value11));

    CHECK_THAT("13'b1100xZ?01"_si[2], exactlyEquals(logic_t::z));

    // extra digits should truncate from the left
    CHECK("4'hxxffa"_si == 10);

    // X and Z leading digits get extended out to the width of the integer
    CHECK_THAT("100'hx10"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("100'bx10"_si[1], exactlyEquals(logic_t(1)));

    // Make sure to check unknown extension with multiple of 64-bit words also.
    CHECK_THAT("100'hxabcdef987654310"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("100'hxabcdef98765431f"_si[1], exactlyEquals(logic_t(1)));

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
    CHECK_THROWS("300'df"_si);
    CHECK_THROWS("300'of"_si);
    CHECK_THROWS(SVInt::fromDigits(1, LiteralBase::Decimal, false, false, nullptr));
}

TEST_CASE("logic_t operators", "[numeric]") {
    logic_t v1(1);
    logic_t v2(0);

    CHECK(v1 == logic_t(1));
    CHECK(v2 != logic_t(1));
    CHECK((v1 | v2) == logic_t(1));
    CHECK((v1 & v2) == logic_t(0));
    CHECK((v1 & v1) == logic_t(1));
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

void checkRoundTrip(std::string str, LiteralBase base) {
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
    CHECK("1'b1"_si.toString() == "1'b1");
    CHECK(SVInt(32, 0, true).toString() == "0");

    ss.str(""); ss << logic_t::x; CHECK(ss.str() == "x");
    ss.str(""); ss << logic_t::z; CHECK(ss.str() == "z");
    ss.str(""); ss << logic_t(1); CHECK(ss.str() == "1");
}

TEST_CASE("Comparison", "[numeric]") {
    CHECK(SVInt(9000) == SVInt(1024, 9000, false));
    CHECK(SVInt(-4) == -4);
    CHECK(SVInt((uint64_t)-4, false) != SVInt(9999, (uint64_t)-4, true));
    CHECK(SVInt(-4) == SVInt(9999, (uint64_t)-4, true));
    CHECK("12'b101"_si == 5);
    CHECK("12'b101"_si != 10);
    CHECK(!bool(!SVInt(4)));
    CHECK(bool(!SVInt(0)));

    CHECK("999'd37"_si < 39);
    CHECK("100'd999999999999999999999999"_si <= "120'd999999999999999999999999"_si);
    CHECK("100'd999999999999999999999999"_si > "120'd999989999999999999999999"_si);
    CHECK("100'd999989999999999999999999"_si < "120'd999999999999999999999999"_si);
    CHECK("100'sd99999999999999999999999999"_si >= "-120'sd999999999999977789999"_si);
    CHECK("100'd99999999999999999999999999"_si < "-120'sd999999999999977789999"_si);
    CHECK("100'd99999999999999999999999999"_si >= -50);

    CHECK(!("-58"_si < "-59"_si));
    CHECK(!("-58"_si < "-58"_si));
    CHECK("-58"_si < "-57"_si);
    CHECK("-58"_si < "57"_si);

    SVInt v(6, 0, false);
    v.setAllOnes();
    CHECK(v == "6'b111111"_si);
    v.setAllZeros();
    CHECK(v == 0);
    v.setAllX();
    CHECK_THAT(v, exactlyEquals("6'bxxxxxx"_si));
    v.setAllZ();
    CHECK_THAT(v, exactlyEquals("6'bzz??ZZ"_si));
    CHECK_THAT("1'bx"_si > 4, exactlyEquals(logic_t::x));

    CHECK_THAT(SVInt(logic_t::x) > SVInt(logic_t::z), exactlyEquals(logic_t::x));

    CHECK(SVInt::conditional(SVInt(1), SVInt(10, 2, false), SVInt(8, 3, false)) == SVInt(2));
    CHECK(SVInt::conditional(SVInt(0), SVInt(7, 2, false), SVInt(12, 3, false)) == SVInt(3));
    CHECK_THAT(SVInt::conditional(SVInt(logic_t::x), "4'bx1z0"_si, "4'bz1x0"_si), exactlyEquals("4'bx1x0"_si));
    CHECK_THAT(SVInt::conditional(SVInt(logic_t::x), "4'b1111"_si, "4'bz1x0"_si), exactlyEquals("4'bx1xx"_si));
}

TEST_CASE("Arithmetic", "[numeric]") {
    CHECK("100'd99999999999"_si + "120'd987654321"_si == "137'd100987654320"_si);
    CHECK("120'd99999999999"_si + "100'd987654321"_si == "137'd100987654320"_si);
    CHECK("100'sd99999999999"_si + "-120'sd999987654321"_si == "-137'sd899987654322"_si);
    CHECK("100'sd32"_si - SVInt(32) == 0);
    CHECK("32'sd32"_si - "100'sd32"_si == 0);
    CHECK("100'sd99999999999"_si * "-120'sd999987654321"_si == "-137'sd99998765431100012345679"_si);
    CHECK("-120'sd999987654321"_si * "0"_si == 0);
    
    CHECK_THAT("100'bx"_si + "98'bx"_si, exactlyEquals("100'bx"_si));
    CHECK_THAT("100'bx"_si - "98'bx"_si, exactlyEquals("100'bx"_si));
    CHECK_THAT("100'bx"_si * "98'bx"_si, exactlyEquals("100'bx"_si));
    CHECK_THAT("100'bx"_si / "98'bx"_si, exactlyEquals("100'bx"_si));
    CHECK_THAT("100'bx"_si % "98'bx"_si, exactlyEquals("100'bx"_si));

    SVInt v1 = "99'd99999999"_si;
    SVInt v2 = v1++;
    CHECK(v2 == "99'd99999999"_si);
    CHECK(v1 == "99'd100000000"_si);

    --v1;
    CHECK(v2 == v1);

    SVInt v3 = "10'bx"_si;
    ++v3;
    CHECK_THAT(v3, exactlyEquals("10'bx"_si));
    v3 = SVInt(4, 1, false);
    ++v3;
    CHECK(v3 == 2);

    SVInt v4 = "10'bx"_si;
    --v4;
    CHECK_THAT(v4, exactlyEquals("10'bx"_si));
    v4 = SVInt(4, 1, false);
    --v4;
    CHECK(v4 == 0);

    SVInt v5 = "-87'sd38"_si;
    v5 /= "3"_si;
    CHECK(v5 == -12);

    SVInt v6 = "-87'sd38"_si;
    v6 %= "3"_si;
    CHECK(v6 == -2);

    CHECK_THAT(-SVInt(logic_t::z), exactlyEquals(SVInt(logic_t::x)));
}

void testDiv(SVInt a, SVInt b, SVInt c) {
    // Test division and remainder using: (a * b + c) / a
    REQUIRE(a >= b);
    REQUIRE(a > c);

    auto p = a * b + c;
    auto q = p / a;
    auto r = p % a;
    CHECK(b == q);
    CHECK(c == r);

    if (b > c) {
        q = p / b;
        r = p % b;
        CHECK(a == q);
        CHECK(c == r);
    }
}

TEST_CASE("Division", "[numeric]") {
    // Division / remainder are very complicated, so split out there tests here.
    CHECK("100'sd99999999999"_si / "-120'sd987654321"_si == SVInt(-101));
    CHECK("100'sd99999999999"_si % "120'sd987654321"_si == SVInt(246913578));
    CHECK((SVInt(64, (uint64_t)-7, true) % SVInt(64, 3, true)) == -1);

    CHECK_THAT("100"_si / "0"_si, exactlyEquals("32'dx"_si));
    CHECK_THAT("100"_si % "0"_si, exactlyEquals("32'dx"_si));

    CHECK("-50"_si / "-50"_si == 1);
    CHECK("-50"_si / "25"_si == -2);
    CHECK("-50"_si % "-40"_si == -10);
    CHECK("-50"_si % "40"_si == -10);

    SVInt v7 = "19823'd234098234098234098234"_si;
    CHECK("300'd0"_si / "10"_si == 0);
    CHECK(v7 / v7 == 1);
    CHECK(v7 / "19823'd234098234098234098235"_si == 0);
    CHECK(v7 / "19823'd11109832458345098"_si == 21071);

    CHECK("300'd0"_si % "10"_si == 0);
    CHECK(v7 % v7 == 0);
    CHECK(v7 % "19823'd234098234098234098235"_si == v7);
    CHECK(v7 % "19823'd11109832458345098"_si == "100'd2954368444538276"_si);

    // Test corner cases of the Knuth division algorithm that are rarely executed.
    testDiv("256'h1ffffffffffffffff"_si, "256'h1ffffffffffffffff"_si, "256'h0"_si);
    testDiv("1024'h112233ceffcecece000000fffffffffffffffffffffffffff"
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            "ffffffffffffffffffffffffffffffff33"_si,

            "1024'h111111fffffffffffffffffffffffffffffffffffffffffff"
            "ffffffffffffffffffffffffffffffffffccfffffffffffffffffff"
            "ffffffffffff00"_si,

            "1024'd7919"_si);

    testDiv("512'hffffffffffffffff00000000000000000000000001"_si,
            "512'h10000000000000001000000000000001"_si,
            "512'h10000000000000000000000000000000"_si);

    testDiv("224'h800000008000000200000005"_si, "224'hfffffffd"_si, "224'h80000000800000010000000f"_si);
    testDiv("256'h80000001ffffffffffffffff"_si, "256'hffffffffffffff0000000"_si, "256'd4219"_si);
    testDiv("4096'd5"_si.shl(2001), "4096'd1"_si.shl(2000), "4096'd54847"_si);
    testDiv("1024'd19"_si.shl(811), "1024'd4356013"_si, "1024'd1"_si);
}

TEST_CASE("Power", "[numeric]") {
    // 0**y
    CHECK(SVInt::Zero.pow(SVInt::Zero) == 1);
    CHECK(SVInt::Zero.pow("20'sb1"_si) == 0);
    CHECK_THAT(SVInt(logic_t::z).pow(SVInt(10)), exactlyEquals("1'bx"_si));
    CHECK_THAT(SVInt::Zero.pow("-2'sb1"_si), exactlyEquals("1'bx"_si));

    // 1**y
    CHECK(SVInt::One.pow(SVInt::Zero) == 1);
    CHECK(SVInt::One.pow("20'sb100"_si) == 1);
    CHECK(SVInt::One.pow("-2'sb1"_si) == 1);
    CHECK_THAT(SVInt::One.pow(SVInt(logic_t::z)), exactlyEquals("1'bx"_si));

    // -1**y
    SVInt neg1(16, (uint64_t)-1, true);
    CHECK(neg1.pow(SVInt::Zero) == 1);
    CHECK(neg1.pow("23'sd1333"_si) == -1);
    CHECK(neg1.pow("23'sd1334"_si) == 1);
    CHECK(neg1.pow("-23'sd1333"_si) == -1);
    CHECK(neg1.pow("-23'sd1334"_si) == 1);

    // -x**y
    SVInt negX(27, (uint64_t)-91835, true);
    CHECK(negX.pow(SVInt::Zero) == 1);
    CHECK(negX.pow("-23'sd1333"_si) == 0);
    CHECK(negX.pow("23'sd33"_si) == 10669765);
    CHECK(negX.pow("23'sd34"_si) == 65763353);

    // x**y
    SVInt posX(27, 901865, true);
    CHECK(posX.pow(SVInt::Zero) == 1);
    CHECK(posX.pow("-23'sd1333"_si) == 0);
    CHECK(posX.pow("23'sd33"_si) == 5792745);
    
    CHECK("-3"_si.pow("3"_si) == "-27"_si);
    CHECK("-3"_si.pow("4"_si) == "81"_si);
    CHECK(SVInt(64, 3, false).pow(SVInt(918245)) == "64'd12951281834385883507"_si);
    CHECK(SVInt(99, 3, false).pow("123'd786578657865786587657658765"_si) == "99'd179325900022335079144376663507"_si);
}

TEST_CASE("Shifting", "[numeric]") {
    CHECK("100'b11110000111"_si.lshr(5) == 60);
    CHECK("64"_si.shl(3) == 512);

    CHECK("129'd12341234"_si.shl(SVInt(129)) == 0);
    CHECK("129'd12341234"_si.shl(129) == 0);
    CHECK("129'd12341234"_si.shl(0) == "129'd12341234"_si);
    CHECK("129'b1"_si.shl(1) == "129'b10"_si);

    CHECK("129'd12341234"_si.lshr(SVInt(129)) == 0);
    CHECK("129'd12341234"_si.lshr(129) == 0);
    CHECK("129'd12341234"_si.lshr(0) == "129'd12341234"_si);

    CHECK("129'd12341234"_si.ashr(SVInt(129)) == 0);
    CHECK("-129'sd12341234"_si.ashr(SVInt(129)) == -1);
    CHECK("129'd12341234"_si.ashr(129) == 0);
    CHECK("-129'sd12341234"_si.ashr(129) == -1);
    CHECK("129'd12341234"_si.ashr(0) == "129'd12341234"_si);
    CHECK("129'sd12341234"_si.ashr(0) == "129'd12341234"_si);

    CHECK_THAT("52'hffxx"_si.shl(4), exactlyEquals("52'hffxx0"_si));
    CHECK_THAT("100'b11xxxZ00101"_si.lshr(7), exactlyEquals("20'b11xx"_si));
    CHECK_THAT("100'b1x"_si.shl(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
    CHECK_THAT("100'b1x"_si.lshr(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
    CHECK_THAT("100'sb1x"_si.ashr(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
}

TEST_CASE("Bitwise", "[numeric]") {
    CHECK_THAT("100'b11xx1Z00x10"_si | "90'b10101xzx01z"_si, exactlyEquals("90'b111x1xxxx1x"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si & "90'b10101xzx01z"_si, exactlyEquals("90'b10x01x00010"_si));
    CHECK_THAT("90'b11xx1Z00x10"_si & "100'b10101xzx01z"_si, exactlyEquals("90'b10x01x00010"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si ^ "90'b10101xzx01z"_si, exactlyEquals("90'b01xx0xxxx0x"_si));
    CHECK_THAT("11'b11xx1Z00x10"_si.xnor("11'b10101xzx01z"_si), exactlyEquals("11'b10xx1xxxx1x"_si));
    CHECK_THAT(~"11'b11xx1Z00x10"_si, exactlyEquals("12'b00xx0x11x01"_si));
    CHECK_THAT(~"6'b101011"_si, exactlyEquals("6'b010100"_si));

    CHECK(("100'b101"_si | "120'b001"_si) == "120'b101"_si);
    CHECK(("100'b101"_si ^ "120'b001"_si) == "120'b100"_si);
    CHECK(("8"_si | "4"_si) == 12);
    CHECK(("8"_si ^ "4"_si) == "32'b1100"_si);

    CHECK_THAT("65'b110"_si.xnor("12'b101"_si), exactlyEquals("65'h1fffffffffffffffc"_si));
    CHECK_THAT("5'b110"_si.xnor("10'b101"_si), exactlyEquals("10'b1111111100"_si));

    CHECK("100'h1000000000000000"_si.reductionOr() == logic_t(1));
    CHECK("100'h10111111111111111111111111111111111"_si.reductionAnd() == logic_t(0));
    CHECK("35'b11111111111111111111111111111111111"_si.reductionAnd() == logic_t(1));
    CHECK("35'b11111100000011111111111111111101110"_si.reductionXor() == logic_t(1));
    CHECK("35'b11111100000011111111111011111101110"_si.reductionXor() == logic_t(0));
    CHECK("66'hfffffffffffffffff"_si.reductionAnd() == logic_t(1));
    CHECK("0"_si.reductionOr() == logic_t(0));
    CHECK("100'd0"_si.reductionOr() == logic_t(0));

    CHECK_THAT("1'bx"_si.reductionAnd(), exactlyEquals(logic_t::x));
    CHECK_THAT("1'bx"_si.reductionOr(), exactlyEquals(logic_t::x));
    CHECK_THAT("1'bx"_si.reductionXor(), exactlyEquals(logic_t::x));
}

TEST_CASE("SVInt misc functions", "[numeric]") {
    CHECK("100'b111"_si.countLeadingZeros() == 97);
    CHECK("128'hffff000000000000ffff000000000000"_si.countLeadingOnes() == 16);
    CHECK("128'hffff000000000000ffff000000000000"_si.countPopulation() == 32);
    CHECK(clog2("900'd982134098123403498298103"_si) == 80);
    CHECK(clog2(SVInt::Zero) == 0);
}
