// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/catch_approx.hpp>
#include <cmath>
#include <sstream>
using Catch::Approx;

#include "slang/numeric/SVInt.h"

TEST_CASE("Construction") {
    SVInt value1;
    SVInt value2(924);
    SVInt value3(924u);
    SVInt value4(61, 924, false);
    SVInt value5(69, (uint64_t)-924, true);
    SVInt value6(-924);
    SVInt value7(63, UINT64_MAX, false);
    SVInt valueA = UINT64_MAX;
    SVInt valueB(logic_t::z);

    CHECK(value1 == 0);
    CHECK(value2 != value1);
    CHECK(value2 == value3);
    CHECK(value4 == value3);
    CHECK(value6 == -924);
    CHECK(value7 == "63'hffffffffffffffff"_si);
    CHECK(SVInt(0) == 0);
    CHECK(SVInt(int64_t(UINT64_MAX)) == -1);
    CHECK_THAT(valueB[0], exactlyEquals(logic_t::z));

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

    CHECK(value5 == value5.resize(69));

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
#    pragma clang diagnostic push
#    pragma clang diagnostic ignored "-Wself-move"
#endif
    value1 = std::move(value1);
#ifdef __clang__
#    pragma clang diagnostic pop
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

    SVInt value12 = "99999'd999999999999999999999999999999999999999999999999999"_si;
    value10 = value12;
    CHECK(value10 == value12);

    CHECK_THAT("13'b1100xZ?01"_si[2], exactlyEquals(logic_t::z));
    CHECK_THAT("13'b1100xZ?01"_si[-1], exactlyEquals(logic_t::x));
    CHECK_THAT("13'b1100xZ?01"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("13'b1100xZ?01"_si[SVInt(8)], exactlyEquals(logic_t(1)));
    CHECK_THAT("13'b1100xZ?01"_si["999'd929293939393939393939"_si], exactlyEquals(logic_t::x));
    CHECK_THAT("13'b1100xZ?01"_si.slice(8, 2), exactlyEquals("7'b1100xZz"_si));

    // extra digits should truncate from the left
    CHECK("4'hxxffa"_si == 10);

    // X and Z leading digits get extended out to the width of the integer
    CHECK_THAT("100'hx10"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("100'bx10"_si[1], exactlyEquals(logic_t(1)));

    // Make sure to check unknown extension with multiple of 64-bit words also.
    CHECK_THAT("100'hxabcdef987654310"_si[99], exactlyEquals(logic_t::x));
    CHECK_THAT("100'hxabcdef98765431f"_si[1], exactlyEquals(logic_t(1)));

#if __cpp_exceptions
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
    CHECK_THROWS(SVInt::fromDigits(1, LiteralBase::Decimal, false, false, {}));
#endif

    // Create from memory pointer.
    uint64_t mem1 = 0x234907862346ff;
    CHECK(SVInt(61, std::span((byte*)&mem1, 8), false).as<uint64_t>() == mem1);

    char mem2[128] = "asdfkljhaw4rkjb234890uKLJNSDF  K@#*)U?:hjn";
    CHECK(SVInt(128 * 8, std::span((byte*)mem2, 128), false).slice(263, 256).as<char>() == '@');

    // Regression test for shrinkToFit with value of 0
    auto value13 = "27'd0"_si;
    value13.shrinkToFit();
    CHECK(value13 == 0);
    CHECK(value13.getBitWidth() == 1);
}

TEST_CASE("logic_t operators") {
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
    CHECK((logic_t(1) && true));

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
    SVInt sv = SVInt::fromString(str);
    str.erase(std::remove(str.begin(), str.end(), '_'), str.end());
    CHECK(sv.toString(base) == str);
}

TEST_CASE("SVInt to string (and back)") {
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
    checkRoundTrip("999999999", LiteralBase::Decimal);
    checkRoundTrip("-2147483648", LiteralBase::Decimal);

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

    ss.str("");
    ss << logic_t::x;
    CHECK(ss.str() == "x");
    ss.str("");
    ss << logic_t::z;
    CHECK(ss.str() == "z");
    ss.str("");
    ss << logic_t(1);
    CHECK(ss.str() == "1");

    // This caught a heap corruption bug in from-string truncation.
    {
        "54'bxx0111x10xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"_si;
    }

    CHECK("96'hx00000Z101"_si.toString(LiteralBase::Decimal, false) == "X");
    CHECK("96'hxxxxxxxxxxxxxxxxxxxxxxxx"_si.toString(LiteralBase::Decimal, false) == "x");
    CHECK("96'hzzzzzzzzzzzzzzzzzzzzzzzz"_si.toString(LiteralBase::Decimal, false) == "z");
    CHECK("96'hzzzzzzzzzzzzzzxzzzzzzzzz"_si.toString(LiteralBase::Decimal, false) == "X");
    CHECK("96'hzzzzzzzzzzzzzz1zzzzzzzzz"_si.toString(LiteralBase::Decimal, false) == "Z");

    CHECK("4'b1xz0"_si.toString(LiteralBase::Hex, false) == "X");
    CHECK("4'bxxxx"_si.toString(LiteralBase::Hex, false) == "x");
    CHECK("4'bzzzz"_si.toString(LiteralBase::Hex, false) == "z");
    CHECK("4'bzz1z"_si.toString(LiteralBase::Hex, false) == "Z");

    // Make sure leading x round trips correctly.
    auto str = "8'b0x"_si.toString(SVInt::MAX_BITS, true);
    CHECK(str == SVInt::fromString(str).toString());
}

TEST_CASE("Comparison") {
    CHECK(SVInt(9000) == SVInt(1024, 9000, false));
    CHECK(SVInt(-4) == -4);
    CHECK(SVInt((uint64_t)-4) != SVInt(9999, (uint64_t)-4, true));
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
    CHECK(SVInt(32, -2147483648, 1) < SVInt(32, -1, 1));
    CHECK(SVInt(32, -1, 1) > SVInt(32, -2147483648, 1));
    CHECK(SVInt(32, 0, 1) > SVInt(32, -1, 1));
    CHECK(SVInt(32, -1, 1) < SVInt(32, 0, 1));

    CHECK(bool("100'd1234"_si && "100'd09809345"_si));
    CHECK(bool("100'd1234"_si || "100'd0"_si));
    CHECK(bool(logic_t::x || "100'd1"_si));

    CHECK(SVInt::logicalEquiv("1234"_si, "98765"_si));
    CHECK(SVInt::logicalImpl("0"_si, "98765"_si));

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
    CHECK_THAT(SVInt::conditional(SVInt(logic_t::x), "4'bx1z0"_si, "4'bz1x0"_si),
               exactlyEquals("4'bx1x0"_si));
    CHECK_THAT(SVInt::conditional(SVInt(logic_t::x), "4'b1111"_si, "4'bz1x0"_si),
               exactlyEquals("4'bx1xx"_si));
}

TEST_CASE("Arithmetic") {
    CHECK("100'd99999999999"_si + "120'd987654321"_si == "137'd100987654320"_si);
    CHECK("120'd99999999999"_si + "100'd987654321"_si == "137'd100987654320"_si);
    CHECK("100'sd99999999999"_si + "-120'sd999987654321"_si == "-137'sd899987654322"_si);
    CHECK("100'sd32"_si - SVInt(32) == 0);
    CHECK("32'sd32"_si - "100'sd32"_si == 0);
    CHECK("100'sd99999999999"_si * "-120'sd999987654321"_si == "-137'sd99998765431100012345679"_si);
    CHECK("-120'sd999987654321"_si * "0"_si == 0);
    CHECK("0"_si * "-120'sd999987654321"_si == 0);

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
    v4--;
    CHECK(v4 == 0);

    SVInt v5 = "-87'sd38"_si;
    v5 /= "3"_si;
    CHECK(v5 == -12);

    SVInt v6 = "-87'sd38"_si;
    v6 %= "3"_si;
    CHECK(v6 == -2);

    SVInt v8 = "87'sd38"_si;
    v8 %= "-3"_si;
    CHECK(v8 == 2);

    CHECK_THAT(-SVInt(logic_t::z), exactlyEquals(SVInt(logic_t::x)));

    SVInt v9 = "193'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF"_si;
    v9++;
    CHECK(v9 == "193'h1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000"_si);

    SVInt v10 = "193'h1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000"_si;
    v10--;
    CHECK(v10 == "193'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF"_si);
}

void testDiv(const SVInt& a, const SVInt& b, const SVInt& c) {
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

TEST_CASE("Division") {
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
    CHECK("-4'sd8"_si / "-4'sd7"_si == 1);

    SVInt v6 = "4"_si / "2"_si;
    CHECK(v6 == 2);
    CHECK(v6.isSigned());

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
            "512'h10000000000000001000000000000001"_si, "512'h10000000000000000000000000000000"_si);

    testDiv("224'h800000008000000200000005"_si, "224'hfffffffd"_si,
            "224'h80000000800000010000000f"_si);
    testDiv("256'h80000001ffffffffffffffff"_si, "256'hffffffffffffff0000000"_si, "256'd4219"_si);
    testDiv("4096'd5"_si.shl(2001), "4096'd1"_si.shl(2000), "4096'd54847"_si);
    testDiv("1024'd19"_si.shl(811), "1024'd4356013"_si, "1024'd1"_si);
}

TEST_CASE("Power") {
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
    CHECK(SVInt(99, 3, false).pow("123'd786578657865786587657658765"_si) ==
          "99'd179325900022335079144376663507"_si);

    CHECK("512'd90871234987239847"_si.pow("512'd9872389712392373"_si).lshr(400) ==
          "512'd3290136519027357223933765911149590"_si);

    // Test huge values. This test is pretty slow so only enable it when building from the CI
    // server.
#ifdef CI_BUILD
    SVInt v =
        "16777215'd999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"_si
            .shl(7000);
    v = v.pow(1234).slice(9000000, 8994500);
    CHECK(v == "5500'd64053931454776197655165648478290003146695"_si);
#endif

    // Test optimization of 2**y.
    SVInt z = SVInt(999, 2, false).pow("934'd934"_si);
    CHECK(z.countOnes() == 1);
    CHECK(z.lshr(934) == 1);
}

TEST_CASE("Shifting") {
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

    CHECK("598'd1234"_si.shl(64).lshr(64) == "598'd1234"_si);

    CHECK_THAT("52'hffxx"_si.shl(4), exactlyEquals("52'hffxx0"_si));
    CHECK_THAT("100'b11xxxZ00101"_si.lshr(7), exactlyEquals("20'b11xx"_si));
    CHECK_THAT("100'b111010110010Z"_si.lshr(1), exactlyEquals("100'b111010110010"_si));
    CHECK_THAT("100'b1x"_si.shl(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
    CHECK_THAT("100'b1x"_si.lshr(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
    CHECK_THAT("100'sb1x"_si.ashr(SVInt(logic_t::x)), exactlyEquals("100'bx"_si));
}

TEST_CASE("Bitwise") {
    CHECK_THAT("100'b11xx1Z00x10"_si | "90'b10101xzx01z"_si, exactlyEquals("90'b111x1xxxx1x"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si & "90'b10101xzx01z"_si, exactlyEquals("90'b10x01x00010"_si));
    CHECK_THAT("90'b11xx1Z00x10"_si & "100'b10101xzx01z"_si, exactlyEquals("90'b10x01x00010"_si));
    CHECK_THAT("100'b11xx1Z00x10"_si ^ "90'b10101xzx01z"_si, exactlyEquals("90'b01xx0xxxx0x"_si));
    CHECK_THAT("11'b11xx1Z00x10"_si.xnor("11'b10101xzx01z"_si),
               exactlyEquals("11'b10xx1xxxx1x"_si));
    CHECK_THAT(~"11'b11xx1Z00x10"_si, exactlyEquals("12'b00xx0x11x01"_si));
    CHECK_THAT(~"6'b101011"_si, exactlyEquals("6'b010100"_si));

    CHECK(("100'b101"_si | "120'b001"_si) == "120'b101"_si);
    CHECK(("100'b101"_si & "120'b001"_si) == "120'b001"_si);
    CHECK(("100'b101"_si ^ "120'b001"_si) == "120'b100"_si);
    CHECK(("8"_si | "4"_si) == 12);
    CHECK(("8"_si & "4"_si) == 0);
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

TEST_CASE("Slicing") {
    SVInt v1 = "7'b1010101"_si;
    v1.set(3, 2, "2'b10"_si);
    CHECK(v1 == "7'b1011001"_si);

    v1.set(9, -2, "12'b11011111011"_si);
    CHECK(v1 == "7'b111110"_si);

    v1.set(9, -2, "12'bx101111101z"_si);
    CHECK(v1 == "7'b111110"_si);

    v1.set(2, 2, "1'bx"_si);
    CHECK_THAT(v1, exactlyEquals("7'b111x10"_si));

    SVInt v2 = "128'b1"_si;
    v2.set(12, 0, "13'b0x"_si);
    CHECK_THAT(v2, exactlyEquals("128'b0x"_si));

    v2.set(0, 0, "1'b0"_si);
    CHECK_THAT(v2, exactlyEquals("128'b0"_si));

    v1.set(9, 9, 0);
    CHECK_THAT(v1.slice(8, -1), exactlyEquals("10'bxx0111x10x"_si));
    CHECK_THAT(v1.slice(8, 0), exactlyEquals("9'bxx0111x10"_si));
    CHECK_THAT(
        v1.slice(8, -65),
        exactlyEquals(
            "74'bxx0111x10xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"_si));
    CHECK_THAT(v2.slice(130, 129), exactlyEquals("2'bxx"_si));

    v1.set(-1, -10, SVInt(10, 0, false));
    CHECK_THAT(v1, exactlyEquals("7'b111x10"_si));

    v1.set(1, 1, 0);
    CHECK_THAT(v1, exactlyEquals("7'b111x00"_si));

    v2.set(12, 0, "13'b0x"_si);
    v2.set(100, 0, SVInt(101, 0, false));
    CHECK(v2 == 0);

    // Test huge values
    SVInt v3 =
        ("16777215'd999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"_si
             .shl(16777000) +
         "16777215'd1234"_si.shl(16777206))
            .slice(16777214, 16777000);
    CHECK(v3.toString(LiteralBase::Decimal) == "215'd47111210086086240918128115148156713906...e27");
    CHECK(v3.toString(LiteralBase::Hex, true) ==
          "215'h728560c56c16d0b0be23da38038624767fffffffffffffffffffff");

    SVInt v4 =
        "16777215'd999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"_si
            .shl(16777000) +
        "16777215'd1234"_si.shl(16777206);
    v4.set(16777001, 16777000, "2'b01"_si);
    CHECK(v4.slice(16777214, 16777000).toString(LiteralBase::Hex, true) ==
          "215'h728560c56c16d0b0be23da38038624767ffffffffffffffffffffd");
}

TEST_CASE("SVInt misc functions") {
    CHECK("100'b111"_si.countLeadingZeros() == 97);
    CHECK("128'hffff000000000000ffff000000000000"_si.countLeadingOnes() == 16);
    CHECK("128'hffffffffffffffffffffffffffffffff"_si.countLeadingOnes() == 128);
    CHECK(clog2("900'd982134098123403498298103"_si) == 80);
    CHECK(clog2(SVInt::Zero) == 0);

    CHECK_THAT("11'bx101011x01z"_si.sext(15), exactlyEquals("15'bxxxxx101011x01z"_si));

    CHECK_THAT((SVInt::One || logic_t::x), exactlyEquals(logic_t(1)));
    CHECK_THAT((SVInt::One && logic_t::x), exactlyEquals(logic_t::x));
    CHECK_THAT((logic_t::x && SVInt::Zero), exactlyEquals(logic_t(0)));

    CHECK(SVInt::concat({}) == SVInt::Zero);

    CHECK(condWildcardEqual("5'b10110"_si, "5'b10110"_si));
    CHECK_THAT(condWildcardEqual("5'bxx101"_si, "5'bxx10x"_si), exactlyEquals(logic_t(1)));
    CHECK_THAT(condWildcardEqual("12'bxx101"_si, "5'bxx10x"_si), exactlyEquals(logic_t::x));
    CHECK_THAT(condWildcardEqual("5'bxx100"_si, "12'bxx101"_si), exactlyEquals(logic_t(0)));
    CHECK_THAT(condWildcardEqual("5'bxx10x"_si, "12'bxx101"_si), exactlyEquals(logic_t::x));

    CHECK(caseZWildcardEqual("5'b10110"_si, "5'b10110"_si));
    CHECK(!caseZWildcardEqual("5'b10010"_si, "5'b10110"_si));
    CHECK(caseZWildcardEqual("7'b??101x0"_si, "5'b101?0"_si));
    CHECK(!caseZWildcardEqual("5'b101?0"_si, "7'bxx101?0"_si));

    CHECK(caseXWildcardEqual("5'b10110"_si, "5'b10110"_si));
    CHECK(!caseXWildcardEqual("5'b10010"_si, "5'b10110"_si));
    CHECK(caseXWildcardEqual("7'b??101x0"_si, "5'b101?0"_si));
    CHECK(caseXWildcardEqual("5'b101?0"_si, "7'bxx101?0"_si));
    CHECK(!caseXWildcardEqual("5'b101?0"_si, "7'bx1101?0"_si));

    CHECK_THAT("7'b10z1110"_si.trunc(5), exactlyEquals("5'bz1110"_si));

    SVInt a = "8'd2"_si;
    a.flattenUnknowns();
    CHECK(a == "8'd2"_si);

    CHECK("128'hffff000000000000ffff00000000000"_si.countOnes() == 32);
    CHECK("128'hffff000000000000ffff00000xz0000"_si.countOnes() == 32);

    CHECK("8'b10010001"_si.countZeros() == 5);
    CHECK("112'hffff00000000ffff00000000000"_si.countZeros() == 80);
    CHECK("112'hffff00000000ffff00000xz0000"_si.countZeros() == 72);

    CHECK("128'hffff000000000000ffff00000000000"_si.countXs() == 0);
    CHECK("128'hffff000000000000ffff0zz00xz0000"_si.countXs() == 4);

    CHECK("128'hffff000000000000ffff00000000000"_si.countZs() == 0);
    CHECK("128'hffff000000000000ffff0zz00xz0000"_si.countZs() == 12);

    CHECK("31'd12345"_si.reverse() == 0x4e060000);
    CHECK("64'd1"_si.reverse() == 1ull << 63);
    CHECK_THAT("129'b1x10"_si.shl(125).reverse(), exactlyEquals("129'b1x1"_si));
    CHECK_THAT("128'b1x10"_si.shl(124).reverse(), exactlyEquals("128'b1x1"_si));

    CHECK("192'hzzxx000000zz0000"_si.countLeadingUnknowns() == 144);
    CHECK("192'hzzxx000000zz0000"_si.countLeadingZs() == 136);
    CHECK(a.countLeadingZs() == 0);
}

TEST_CASE("Double conversions") {
    CHECK("112'b1xxx1"_si.toDouble() == 17.0);
    CHECK("112'd0"_si.toDouble() == 0.0);
    CHECK("-112'sd9223372036854775808"_si.toDouble() == -9223372036854775808.0);
    CHECK("112'sd9223372036854775807"_si.toDouble() == 9223372036854775807.0);
    CHECK("-112'sd9223372036854775809"_si.toDouble() == -9223372036854775809.0);

    CHECK("112'd18446744073709551615"_si.toDouble() == 18446744073709551615.0);
    CHECK("112'd18446744073709551616"_si.toDouble() == 18446744073709551616.0);

    // Each of these test cases hits a specific rounding case in the conversion code.
    CHECK("112'd36893488147419103230"_si.toDouble() == 36893488147419103230.0);
    CHECK("112'd36893488147419107328"_si.toDouble() == 36893488147419107328.0);
    CHECK("112'd36893488147419115520"_si.toDouble() == 36893488147419115520.0);
    CHECK("128'd332306998946229005119439912489189377"_si.toDouble() ==
          332306998946229005119439912489189377.0);

    // Test overflow.
    CHECK("2048'd1"_si.shl(1024).toDouble() == INFINITY);
    CHECK("-2048'sd1"_si.shl(1024).toDouble() == -INFINITY);

    CHECK(SVInt::fromDouble(112, 0.0, false) == "112'd0"_si);
    CHECK(SVInt::fromDouble(112, 0.49999999999999, false) == "112'd0"_si);
    CHECK(SVInt::fromDouble(112, 0.5, false) == "112'd1"_si);
    CHECK(SVInt::fromDouble(112, 0.5, false, false) == "112'd0"_si);
    CHECK(SVInt::fromDouble(112, 0.8987, false) == "112'd1"_si);
    CHECK(SVInt::fromDouble(16, 1.0, false) == "16'd1"_si);
    CHECK(SVInt::fromDouble(16, 1024.499999, false) == "16'd1024"_si);
    CHECK(SVInt::fromDouble(16, 1024.5, false) == "16'd1025"_si);
    CHECK(SVInt::fromDouble(16, 1024.999, false, false) == "16'd1024"_si);
    CHECK(SVInt::fromDouble(112, 36893488147419107328.0, false) == "112'd36893488147419103232"_si);

    CHECK(SVInt::fromDouble(112, -0.0, true) == "112'sd0"_si);
    CHECK(SVInt::fromDouble(112, -0.49999999999999, true) == "112'sd0"_si);
    CHECK(SVInt::fromDouble(112, -0.5, true) == "-112'sd1"_si);
    CHECK(SVInt::fromDouble(112, -0.5, true, false) == "112'sd0"_si);
    CHECK(SVInt::fromDouble(112, -0.8987, true) == "-112'sd1"_si);
    CHECK(SVInt::fromDouble(16, -1.0, true) == "-16'sd1"_si);
    CHECK(SVInt::fromDouble(16, -1024.499999, true) == "-16'sd1024"_si);
    CHECK(SVInt::fromDouble(16, -1024.5, true) == "-16'sd1025"_si);
    CHECK(SVInt::fromDouble(112, -36893488147419107328.0, true) ==
          "-112'sd36893488147419103232"_si);

    CHECK(SVInt::fromDouble(19, NAN, true) == "19'sd0"_si);
    CHECK(SVInt::fromDouble(19, INFINITY, true) == "19'sd0"_si);
    CHECK(SVInt::fromDouble(19, -INFINITY, true) == "19'sd0"_si);
}

TEST_CASE("Float conversions") {
    CHECK("112'b1xxx1"_si.toFloat() == 17.0f);
    CHECK("112'd0"_si.toFloat() == 0.0f);
    CHECK("-112'sd2147483648"_si.toFloat() == -2147483648.0f);
    CHECK("112'sd2147483648"_si.toFloat() == 2147483648.0f);
    CHECK("-112'sd2147483650"_si.toFloat() == -2147483650.0f);

    CHECK("112'd18446744073709551615"_si.toFloat() == 18446744073709551615.0f);
    CHECK("112'd18446744073709551616"_si.toFloat() == 18446744073709551616.0f);

    CHECK("112'd36893488147419103230"_si.toFloat() == 36893488147419103230.0f);
    CHECK("112'd36893488147419107328"_si.toFloat() == 36893488147419107328.0f);
    CHECK("112'd36893488147419115520"_si.toFloat() == 36893488147419115520.0f);
    CHECK("128'd332306998946229005119439912489189377"_si.toFloat() ==
          332306998946229005119439912489189377.0f);

    // Test overflow.
    CHECK("2048'd1"_si.shl(128).toFloat() == INFINITY);
    CHECK("-2048'sd1"_si.shl(128).toFloat() == -INFINITY);

    CHECK(SVInt::fromFloat(112, 0.0f, false) == "112'd0"_si);
    CHECK(SVInt::fromFloat(112, 0.4999999f, false) == "112'd0"_si);
    CHECK(SVInt::fromFloat(112, 0.5f, false) == "112'd1"_si);
    CHECK(SVInt::fromFloat(112, 0.5f, false, false) == "112'd0"_si);
    CHECK(SVInt::fromFloat(112, 0.8987f, false) == "112'd1"_si);
    CHECK(SVInt::fromFloat(16, 1.0f, false) == "16'd1"_si);
    CHECK(SVInt::fromFloat(16, 1024.4999f, false) == "16'd1024"_si);
    CHECK(SVInt::fromFloat(16, 1024.5f, false) == "16'd1025"_si);
    CHECK(SVInt::fromFloat(112, 36893488147419107328.0f, false) == "112'd36893488147419103232"_si);

    CHECK(SVInt::fromFloat(112, -0.0f, true) == "112'sd0"_si);
    CHECK(SVInt::fromFloat(112, -0.4999999f, true) == "112'sd0"_si);
    CHECK(SVInt::fromFloat(112, -0.5f, true) == "-112'sd1"_si);
    CHECK(SVInt::fromFloat(112, -0.5f, true, false) == "112'sd0"_si);
    CHECK(SVInt::fromFloat(112, -0.8987f, true) == "-112'sd1"_si);
    CHECK(SVInt::fromFloat(16, -1.0f, true) == "-16'sd1"_si);
    CHECK(SVInt::fromFloat(16, -1024.4999f, true) == "-16'sd1024"_si);
    CHECK(SVInt::fromFloat(16, -1024.5f, true) == "-16'sd1025"_si);
    CHECK(SVInt::fromFloat(16, -1024.999f, true, false) == "-16'sd1024"_si);
    CHECK(SVInt::fromFloat(112, -36893488147419107328.0f, true) ==
          "-112'sd36893488147419103232"_si);

    CHECK(SVInt::fromFloat(19, NAN, true) == "19'sd0"_si);
    CHECK(SVInt::fromFloat(19, INFINITY, true) == "19'sd0"_si);
    CHECK(SVInt::fromFloat(19, -INFINITY, true) == "19'sd0"_si);
}

using namespace Catch::literals;

TEST_CASE("Time scaling") {
    static constexpr double ep = std::numeric_limits<double>::epsilon() * 10;
#define AP(v) Approx(v).epsilon(ep)

    auto tv = [](std::string_view str) { return TimeScaleValue::fromString(str).value(); };
    auto ts = [](std::string_view str) { return TimeScale::fromString(str).value(); };

    TimeScale scale = ts("100ns / 1ps");
    CHECK(scale.apply(234.0567891, TimeUnit::Nanoseconds, true) == AP(2.34057));
    CHECK(scale.apply(234.0567891, TimeUnit::Picoseconds, true) == AP(0.00234));
    CHECK(scale.apply(234.0567891, TimeUnit::Seconds, true) == AP(2.340567891e9));

    scale.base = tv("10ps");
    CHECK(scale.apply(234.0567891, TimeUnit::Nanoseconds, true) == AP(23405.7));
    CHECK(scale.apply(234.0567891, TimeUnit::Picoseconds, true) == AP(23.4));
    CHECK(scale.apply(234.0567891, TimeUnit::Seconds, true) == AP(2.340567891e13));

    scale.base = tv("1ms");
    CHECK(scale.apply(234.0567891, TimeUnit::Nanoseconds, true) == AP(0.000234057));
    CHECK(scale.apply(234.0567891, TimeUnit::Picoseconds, true) == AP(2.34e-7));
    CHECK(scale.apply(234.0567891, TimeUnit::Seconds, true) == AP(234056.7891));

    scale.base = tv("1ns");
    scale.precision = tv("1ns");
    CHECK(scale.apply(234.0567891, TimeUnit::Nanoseconds, true) == AP(234));
    CHECK(scale.apply(234.0567891, TimeUnit::Picoseconds, true) == AP(0));
    CHECK(scale.apply(234.0567891, TimeUnit::Seconds, true) == AP(234056789100));
}

TEST_CASE("TimeScale stringify") {
    CHECK(!TimeScale::fromString("").has_value());
    CHECK(!TimeScale::fromString("foo").has_value());
    CHECK(!TimeScale::fromString("3.4 ps").has_value());
    CHECK(!TimeScale::fromString("3    ps").has_value());
    CHECK(!TimeScale::fromString("3").has_value());
    CHECK(!TimeScale::fromString("3    ds").has_value());
    CHECK(!TimeScale::fromString("3    pd").has_value());
    CHECK(!TimeScale::fromString("1 ns").has_value());
    CHECK(!TimeScale::fromString("1 ns d 1 ns").has_value());
    CHECK(!TimeScale::fromString("1 ns /  ").has_value());
    CHECK(!TimeScale::fromString("1 ns / 1bb").has_value());
    CHECK(!TimeScale::fromString("1 ns / 1ns fff").has_value());
    CHECK(!TimeScale::fromString("10ns/10ms").has_value());

    CHECK(!TimeScaleValue::fromString("1 nssss").has_value());

    std::ostringstream ss;
    ss << *TimeScaleValue::fromString("1ns") << *TimeScale::fromString("1ns/1ps");
    CHECK(ss.str() == "1ns1ns / 1ps");

    CHECK(TimeScaleValue::fromString("100s")->toString() == "100s");
    CHECK(TimeScale::fromString("10   ms    /   10    us")->toString() == "10ms / 10us");

    size_t length;
    CHECK(!suffixToTimeUnit("", length).has_value());
}

TEST_CASE("SVInt operator crash regression GH #469") {
    auto tree = SyntaxTree::fromText(R"(
if mlog2 (32'd1;
function mlog2
input [1024 : 0 value
for ;
value > 32'd0
value = value >> 1
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}
