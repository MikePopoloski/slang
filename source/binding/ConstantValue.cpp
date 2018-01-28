//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "ConstantValue.h"

namespace slang {

const ConstantValue ConstantValue::Invalid;

optional<int> ConstantValue::coerceInteger(uint32_t maxBits, Diagnostics*, SourceLocation) const {
    // TODO: report errors
    if (isInteger()) {
        const SVInt& intVal = integer();
        if (!intVal.hasUnknown() && intVal.getActiveBits() <= maxBits) {
            auto result = intVal.as<int>();
            if (result)
                return *result;
        }
    }
    return std::nullopt;
}

}
