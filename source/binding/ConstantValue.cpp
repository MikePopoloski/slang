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

ConstantRange ConstantRange::subrange(ConstantRange select) const {
    int32_t l = lower();
    ConstantRange result;
    result.left = select.lower() + l;
    result.right = select.upper() + l;

    ASSERT(result.right <= upper());
    if (isLittleEndian())
        return result;
    else
        return result.reverse();
}

void to_json(json& j, const ConstantValue& cv) {
    std::visit([&j](auto&& arg) noexcept {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            j = "<unset>";
        else if constexpr (std::is_same_v<T, SVInt>)
            j = arg.toString();
        else if constexpr (std::is_same_v<T, double>)
            j = arg;
        else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
            j = "null";
        else
            static_assert(always_false<T>::value, "Missing case");
    }, cv.value);
}

ConstantValue LValue::load() const {
    return std::visit([](auto&& arg)
                      noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat>) -> ConstantValue {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            return ConstantValue();
        else if constexpr (std::is_same_v<T, ConstantValue*>)
            return *arg;
        else if constexpr (std::is_same_v<T, CVRange>) {
            ConstantValue& cv = *arg.cv;
            if (!cv)
                return ConstantValue();

            return cv.integer().slice(arg.range.upper(), arg.range.lower());
        }
        else if constexpr (std::is_same_v<T, Concat>)
            THROW_UNREACHABLE; // TODO: handle this case
        else
            static_assert(always_false<T>::value, "Missing case");
    }, value);
}

void LValue::store(const ConstantValue& newValue) {
    std::visit([&newValue](auto&& arg)
               noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat> &&
                        !std::is_same_v<std::decay_t<decltype(arg)>, CVRange>) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            return;
        else if constexpr (std::is_same_v<T, ConstantValue*>)
            *arg = newValue;
        else if constexpr (std::is_same_v<T, CVRange>) {
            ConstantValue& cv = *arg.cv;
            ASSERT(cv);

            THROW_UNREACHABLE; // TODO: handle this
        }
        else if constexpr (std::is_same_v<T, Concat>)
            THROW_UNREACHABLE; // TODO: handle this case
        else
            static_assert(always_false<T>::value, "Missing case");
    }, value);
}

LValue LValue::selectRange(ConstantRange range) const {
    return std::visit([&range](auto&& arg) -> LValue {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            return nullptr;
        else if constexpr (std::is_same_v<T, ConstantValue*>)
            return LValue(*arg, range);
        else if constexpr (std::is_same_v<T, CVRange>)
            return LValue(*arg.cv, arg.range.subrange(range));
        else if constexpr (std::is_same_v<T, Concat>)
            THROW_UNREACHABLE;
        else
            static_assert(always_false<T>::value, "Missing case");
    }, value);
}

}
