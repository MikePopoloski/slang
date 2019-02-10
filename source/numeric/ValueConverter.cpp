//------------------------------------------------------------------------------
// ValueConverter.cpp
// Compile-time constant value type conversion.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/numeric/ValueConverter.h"

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/TypeSymbols.h"

namespace slang {

SVInt ValueConverter::intToInt(const SVInt& integer, bitwidth_t width, bool isSigned) {
    // TODO: handle four state changes
    // TODO: sign handling is not quite right
    SVInt result = integer;
    result.setSigned(isSigned);

    bitwidth_t oldWidth = result.getBitWidth();
    if (oldWidth != width) {
        if (width < oldWidth) {
            // TODO: add a truncate() method
            return result.slice((int32_t)width - 1, 0);
        }
        else {
            return extend(result, width, result.isSigned());
        }
    }

    return result;
}

std::string ValueConverter::intToStr(const SVInt& integer) {
    // Conversion is described in [6.16]: take each 8 bit chunk,
    // remove it if it's zero, otherwise add as character to the string.
    int32_t msb = int32_t(integer.getBitWidth() - 1);
    int32_t extraBits = int32_t(integer.getBitWidth() % 8);

    std::string result;
    if (extraBits) {
        auto c = integer.slice(msb, msb - extraBits + 1).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= extraBits;
    }

    while (msb >= 7) {
        auto c = integer.slice(msb, msb - 7).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= 8;
    }

    return result;
}

double ValueConverter::intToFloat(const SVInt& integer) {
    // TODO: make this more robust
    return (double)integer.as<int64_t>().value();
}

} // namespace slang