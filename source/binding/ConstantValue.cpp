//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "ConstantValue.h"

#include "json.hpp"

namespace slang {

const ConstantValue ConstantValue::Invalid;

void to_json(json& j, const ConstantValue& cv) {
    switch (cv.value.index()) {
        case 0: j = "<unset>"; break;
        case 1: j = cv.integer().toString(); break;
        case 2: j = cv.real(); break;
        case 3: j = "null"; break;
        default:
            THROW_UNREACHABLE;
    }
}

}
