//------------------------------------------------------------------------------
// LValue.cpp
// Compile-time lvalue representation (for constant evaluation)
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/LValue.h"

#include <ostream>

namespace slang::ast {

template<typename T>
struct always_false : std::false_type {};

ConstantValue* LValue::resolve() {
    if (!std::holds_alternative<Path>(value))
        return nullptr;

    std::optional<ConstantRange> range;
    ConstantValue* target = resolveInternal(range);

    // If there is no singular target, return nullptr to indicate.
    if (range.has_value())
        return nullptr;

    return target;
}

ConstantValue LValue::load() const {
    if (bad())
        return nullptr;

    auto concat = std::get_if<Concat>(&value);
    if (concat) {
        if (concat->kind == Concat::Packed) {
            SmallVector<SVInt> vals;
            vals.reserve(concat->elems.size());
            for (auto& elem : concat->elems)
                vals.push_back(elem.load().integer());
            return SVInt::concat(vals);
        }
        else {
            std::vector<ConstantValue> vals;
            vals.reserve(concat->elems.size());
            for (auto& elem : concat->elems)
                vals.push_back(elem.load());
            return vals;
        }
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
                    if (arg.forceOutOfBounds) {
                        result = arg.defaultValue;
                    }
                    else if (result.isUnion()) {
                        // If we're selecting the active member all is well. If not,
                        // we need to return the default value because we have no
                        // idea what type this should be.
                        if (arg.index < 0 || result.unionVal()->activeMember != uint32_t(arg.index))
                            result = arg.defaultValue;
                    }
                    else if (arg.index < 0 || size_t(arg.index) >= result.size()) {
                        result = arg.defaultValue;
                    }
                    else if (result.isString()) {
                        result = SVInt(8, (uint64_t)result.str()[size_t(arg.index)], false);
                    }
                    else {
                        // Be careful not to assign to the result while
                        // still referencing its elements.
                        ConstantValue temp(std::move(result.at(size_t(arg.index))));
                        result = std::move(temp);
                    }
                }
                else if constexpr (std::is_same_v<T, ArraySlice>) {
                    result = result.getSlice(arg.range.upper(), arg.range.lower(),
                                             arg.defaultValue);
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
        if (concat->kind == Concat::Packed) {
            // Divide up the value among all of the concatenated lvalues.
            auto& sv = newValue.integer();
            int32_t msb = (int32_t)sv.getBitWidth() - 1;
            for (auto& elem : concat->elems) {
                int32_t width = (int32_t)elem.load().integer().getBitWidth();
                elem.store(sv.slice(msb, msb - width + 1));
                msb -= width;
            }
        }
        else {
            auto newElems = newValue.elements();
            auto& lvalElems = concat->elems;
            SLANG_ASSERT(newElems.size() == lvalElems.size());
            for (size_t i = 0; i < lvalElems.size(); i++)
                lvalElems[i].store(newElems[i]);
        }
        return;
    }

    std::optional<ConstantRange> range;
    ConstantValue* target = resolveInternal(range);
    if (!target || target->bad())
        return;

    // We have the final target, now assign to it.
    // If there is no range specified, we should be able to assign straight to the target.
    if (!range) {
        // If this is a queue with a max bound make sure to limit the assigned value.
        if (target->isQueue()) {
            auto& dest = *target->queue();
            if (dest.maxBound) {
                auto& src = *newValue.queue();
                size_t size = std::min<size_t>(dest.maxBound + 1, src.size());
                dest.resize(size);
                for (size_t i = 0; i < size; i++)
                    dest[i] = src[i];
                return;
            }
        }

        *target = newValue;
        return;
    }

    // Otherwise, assign to the slice.
    if (target->isInteger()) {
        target->integer().set(range->upper(), range->lower(), newValue.integer());
    }
    else if (target->isString()) {
        SLANG_ASSERT(range->left == range->right);
        SLANG_ASSERT(range->left >= 0);

        char c = (char)*newValue.integer().as<uint8_t>();
        if (c)
            target->str()[size_t(range->left)] = c;
    }
    else if (target->isQueue()) {
        int32_t l = range->lower();
        int32_t u = range->upper();

        auto& src = *newValue.queue();
        auto& dest = *target->queue();

        u = std::min(u, int32_t(dest.size()));
        for (int32_t i = std::max(l, 0); i <= u; i++)
            dest[size_t(i)] = src[size_t(i - l)];
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

ConstantValue* LValue::resolveInternal(std::optional<ConstantRange>& range) {
    auto& path = std::get<Path>(value);
    ConstantValue* target = path.base;

    for (auto& elem : path.elements) {
        if (!target || target->bad())
            break;

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
                    if (arg.forceOutOfBounds) {
                        target = nullptr;
                    }
                    else if (target->isQueue()) {
                        auto& q = *target->queue();
                        if (arg.index < 0 || (q.maxBound && uint32_t(arg.index) > q.maxBound)) {
                            target = nullptr;
                        }
                        else {
                            // Queues can reference one past the end to insert a new element.
                            size_t idx = size_t(arg.index);
                            if (idx == q.size())
                                q.push_back(arg.defaultValue);

                            if (idx >= q.size())
                                target = nullptr;
                            else
                                target = &q[size_t(arg.index)];
                        }
                    }
                    else if (target->isUnion()) {
                        SLANG_ASSERT(arg.index >= 0);

                        auto& unionVal = target->unionVal();
                        if (unionVal->activeMember != uint32_t(arg.index)) {
                            unionVal->activeMember = uint32_t(arg.index);
                            unionVal->value = arg.defaultValue;
                        }
                        target = &unionVal->value;
                    }
                    else if (target->isString()) {
                        if (arg.index < 0 || size_t(arg.index) >= target->str().size())
                            target = nullptr;
                        else
                            range = ConstantRange{arg.index, arg.index};
                    }
                    else {
                        auto elems = target->elements();
                        if (arg.index < 0 || size_t(arg.index) >= elems.size())
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
                    auto [it, inserted] = map.try_emplace(std::move(arg.index),
                                                          std::move(arg.defaultValue));

                    target = &it->second;
                }
                else {
                    static_assert(always_false<T>::value, "Missing case");
                }
            },
            elem);
    }

    return target;
}

void LValue::addBitSlice(ConstantRange range) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace_back(BitSlice{range});
}

void LValue::addIndex(int32_t index, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace_back(ElementIndex{index, std::move(defaultValue), false});
}

void LValue::addIndexOutOfBounds(ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace_back(ElementIndex{0, std::move(defaultValue), true});
}

void LValue::addArraySlice(ConstantRange range, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace_back(ArraySlice{range, std::move(defaultValue)});
}

void LValue::addArrayLookup(ConstantValue&& index, ConstantValue&& defaultValue) {
    if (bad())
        return;

    auto& elems = std::get<Path>(value).elements;
    elems.emplace_back(ArrayLookup{std::move(index), std::move(defaultValue)});
}

} // namespace slang::ast
