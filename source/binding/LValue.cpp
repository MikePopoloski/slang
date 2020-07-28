//------------------------------------------------------------------------------
// LValue.cpp
// Compile-time lvalue representation (for constant evaluation)
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/LValue.h"

namespace slang {

template<typename T>
struct always_false : std::false_type {};

ConstantValue LValue::load() const {
    if (bad())
        return nullptr;

    auto concat = std::get_if<Concat>(&value);
    if (concat) {
        SmallVectorSized<SVInt, 4> vals;
        for (auto& elem : *concat)
            vals.append(elem.load().integer());
        return SVInt::concat(vals);
    }

    // Otherwise, we have an lvalue path. Walk the path and apply each element.
    auto& path = std::get<Path>(value);
    ConstantValue result = *path.base;
    for (auto& elem : path.elements) {
        if (!result)
            return nullptr;

        std::visit(
            [&result](auto&& arg) {
                using T = std::decay_t<decltype(arg)>;
                if constexpr (std::is_same_v<T, BitSlice>) {
                    result = result.getSlice(arg.range.upper(), arg.range.lower(), nullptr);
                }
                else if constexpr (std::is_same_v<T, ElementIndex>) {
                    if (result.isString()) {
                        result = SVInt(8, (uint64_t)result.str()[size_t(arg.index)], false);
                    }
                    else {
                        auto elems = result.elements();
                        if (arg.index < 0 || arg.index >= elems.size())
                            result = arg.defaultValue;
                        else {
                            // Be careful not to assign to the result while
                            // still referencing its elements.
                            ConstantValue temp(std::move(elems[size_t(arg.index)]));
                            result = std::move(temp);
                        }
                    }
                }
                else if constexpr (std::is_same_v<T, ArraySlice>) {
                    result =
                        result.getSlice(arg.range.upper(), arg.range.lower(), arg.defaultValue);
                }
                else if constexpr (std::is_same_v<T, ArrayLookup>) {
                    auto& map = *result.map();
                    if (auto it = map.find(arg.index); it != map.end()) {
                        // If we find the index in the target map, return the value.
                        ConstantValue temp(std::move(it->second));
                        result = std::move(temp);
                    }
                    else if (map.defaultValue) {
                        // Otherwise, if the map itself has a default set, use that.
                        ConstantValue temp(std::move(map.defaultValue));
                        result = std::move(temp);
                    }
                    else {
                        // Finally, fall back on whatever the default default is.
                        result = arg.defaultValue;
                    }
                }
                else {
                    static_assert(always_false<T>::value, "Missing case");
                }
            },
            elem);
    }

    return result;
}

void LValue::store(const ConstantValue& newValue) {
    if (bad())
        return;

    auto concat = std::get_if<Concat>(&value);
    if (concat) {
        // Divide up the value among all of the concatenated lvalues.
        auto& sv = newValue.integer();
        int32_t msb = (int32_t)sv.getBitWidth() - 1;
        for (auto& elem : *concat) {
            int32_t width = (int32_t)elem.load().integer().getBitWidth();
            elem.store(sv.slice(msb, msb - width + 1));
            msb -= width;
        }
        return;
    }

    // Otherwise, we have an lvalue path. Walk the path and apply each element.
    auto& path = std::get<Path>(value);
    ConstantValue* target = path.base;
    optional<ConstantRange> range;

    for (auto& elem : path.elements) {
        if (!target || target->bad())
            return;

        std::visit(
            [&target, &range](auto&& arg) {
                using T = std::decay_t<decltype(arg)>;
                if constexpr (std::is_same_v<T, BitSlice>) {
                    if (!range)
                        range = arg.range;
                    else
                        range = range->subrange(arg.range);
                }
                else if constexpr (std::is_same_v<T, ElementIndex>) {
                    if (target->isString()) {
                        range = ConstantRange{ arg.index, arg.index };
                    }
                    else {
                        auto elems = target->elements();
                        if (arg.index < 0 || arg.index >= elems.size())
                            target = nullptr;
                        else
                            target = &elems[size_t(arg.index)];
                    }
                }
                else if constexpr (std::is_same_v<T, ArraySlice>) {
                    range = arg.range;
                }
                else if constexpr (std::is_same_v<T, ArrayLookup>) {
                    auto& map = *target->map();
                    auto [it, inserted] =
                        map.try_emplace(std::move(arg.index), std::move(arg.defaultValue));

                    target = &it->second;
                }
                else {
                    static_assert(always_false<T>::value, "Missing case");
                }
            },
            elem);
    }

    if (!target || target->bad())
        return;

    // We have the final target, now assign to it.
    // If there is no range specified, we should be able to assign straight to the target.
    if (!range) {
        *target = newValue;
        return;
    }

    // Otherwise, assign to the slice.
    if (target->isInteger()) {
        target->integer().set(range->upper(), range->lower(), newValue.integer());
    }
    else if (target->isString()) {
        ASSERT(range->left == range->right);
        ASSERT(range->left >= 0);

        char c = (char)*newValue.integer().as<uint8_t>();
        if (c)
            target->str()[size_t(range->left)] = c;
    }
    else {
        int32_t l = range->lower();
        int32_t u = range->upper();

        auto src = newValue.elements();
        auto dest = target->elements();

        u = std::min(u, int32_t(dest.size()));
        for (int32_t i = std::max(l, 0); i <= u; i++)
            dest[size_t(i)] = src[size_t(i - l)];
    }
}

void LValue::addBitSlice(ConstantRange range) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace(BitSlice{ range });
}

void LValue::addIndex(int32_t index, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace(ElementIndex{ index, std::move(defaultValue) });
}

void LValue::addArraySlice(ConstantRange range, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace(ArraySlice{ range, std::move(defaultValue) });
}

void LValue::addArrayLookup(ConstantValue&& index, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace(ArrayLookup{ std::move(index), std::move(defaultValue) });
}

} // namespace slang