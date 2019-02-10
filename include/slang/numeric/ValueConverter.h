//------------------------------------------------------------------------------
// ValueConverter.h
// Compile-time constant value type conversion.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/numeric/SVInt.h"

namespace slang {

class ConstantValue;

class ValueConverter {
public:
    static SVInt intToInt(const SVInt& integer, bitwidth_t width, bool isSigned);
    static std::string intToStr(const SVInt& integer);
    static double intToFloat(const SVInt& integer);
};

} // namespace slang