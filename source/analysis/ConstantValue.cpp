//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "ConstantValue.h"

namespace slang {

std::optional<int> ConstantValue::coerceInteger(uint32_t maxBits, Diagnostics* diagnostics,
                                                SourceLocation location) {
    // TODO: report errors
    if (isInteger()) {
        const SVInt& value = integer();
        if (!value.hasUnknown() && value.getActiveBits() <= maxBits) {
            auto result = value.asBuiltIn<int>();
            if (result)
                return *result;
        }
    }
    return std::nullopt;
}

}