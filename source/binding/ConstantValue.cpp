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
    std::visit([&j](auto&& arg) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            j = "<unset>";
        else if constexpr (std::is_same_v<T, SVInt>)
            j = arg.toString();
        else if constexpr (std::is_same_v<T, double>)
            j = arg;
        else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
            j = "null";
        else if constexpr (std::is_same_v<T, LValue>)
            // TODO: print out lvalues
            j = "TODO";
        else
            static_assert(always_false<T>::value, "Missing case");
    }, cv.value);
}

}
