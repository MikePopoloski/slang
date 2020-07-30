//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/numeric/ConstantValue.h"

#include "../text/FormatBuffer.h"
#include <fmt/format.h>

#include "slang/util/Hash.h"

namespace slang {

template<typename T>
struct always_false : std::false_type {};

const ConstantValue ConstantValue::Invalid;

std::string ConstantValue::toString() const {
    return std::visit(
        [](auto&& arg) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return "<unset>"s;
            else if constexpr (std::is_same_v<T, SVInt>)
                return arg.toString();
            else if constexpr (std::is_same_v<T, real_t>)
                return fmt::format("{}", double(arg));
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return fmt::format("{}", float(arg));
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return "null"s;
            else if constexpr (std::is_same_v<T, Elements>) {
                FormatBuffer buffer;
                buffer.append("[");
                for (auto& element : arg) {
                    buffer.append(element.toString());
                    buffer.append(",");
                }

                if (!arg.empty())
                    buffer.pop_back();
                buffer.append("]");
                return buffer.str();
            }
            else if constexpr (std::is_same_v<T, std::string>)
                return arg;
            else if constexpr (std::is_same_v<T, Map>) {
                FormatBuffer buffer;
                buffer.append("[");
                for (auto& [key, val] : *arg)
                    buffer.format("{}:{},", key.toString(), val.toString());

                if (arg->defaultValue)
                    buffer.format("default:{}", arg->defaultValue.toString());
                else if (!arg->empty())
                    buffer.pop_back();

                buffer.append("]");
                return buffer.str();
            }
            else if constexpr (std::is_same_v<T, Queue>) {
                FormatBuffer buffer;
                buffer.append("[");
                for (auto& element : *arg) {
                    buffer.append(element.toString());
                    buffer.append(",");
                }

                if (!arg->empty())
                    buffer.pop_back();
                buffer.append("]");
                return buffer.str();
            }
            else
                static_assert(always_false<T>::value, "Missing case");
        },
        value);
}

size_t ConstantValue::hash() const {
    size_t h = value.index();
    std::visit(
        [&h](auto&& arg) noexcept {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                hash_combine(h, 0);
            else if constexpr (std::is_same_v<T, SVInt>)
                hash_combine(h, arg.hash());
            else if constexpr (std::is_same_v<T, real_t>)
                hash_combine(h, std::hash<double>()(arg));
            else if constexpr (std::is_same_v<T, shortreal_t>)
                hash_combine(h, std::hash<float>()(arg));
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                hash_combine(h, 0);
            else if constexpr (std::is_same_v<T, Elements>) {
                for (auto& element : arg)
                    hash_combine(h, element.hash());
            }
            else if constexpr (std::is_same_v<T, std::string>)
                hash_combine(h, std::hash<std::string>()(arg));
            else if constexpr (std::is_same_v<T, Map>) {
                for (auto& [key, val] : *arg) {
                    hash_combine(h, key.hash());
                    hash_combine(h, val.hash());
                }
            }
            else if constexpr (std::is_same_v<T, Queue>) {
                for (auto& element : *arg)
                    hash_combine(h, element.hash());
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        value);
    return h;
}

ConstantValue ConstantValue::getSlice(int32_t upper, int32_t lower,
                                      const ConstantValue& defaultValue) const {
    if (isInteger())
        return integer().slice(upper, lower);

    if (isUnpacked()) {
        span<const ConstantValue> elems = elements();
        std::vector<ConstantValue> result{ size_t(upper - lower + 1) };
        ConstantValue* dest = result.data();

        for (int32_t i = lower; i <= upper; i++) {
            if (i < 0 || size_t(i) >= elems.size())
                *dest++ = defaultValue;
            else
                *dest++ = elems[size_t(i)];
        }

        return result;
    }

    if (isQueue()) {
        auto& q = *queue();
        SVQueue result;
        for (int32_t i = lower; i <= upper; i++) {
            if (i >= 0 && i < q.size())
                result.push_back(q[size_t(i)]);
        }

        return result;
    }

    if (isString()) {
        ASSERT(upper == lower);
        ASSERT(upper >= 0);
        return SVInt(8, (uint64_t)str()[size_t(upper)], false);
    }

    return nullptr;
}

bool ConstantValue::isTrue() const {
    return std::visit(
        [](auto&& arg) noexcept {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, SVInt>)
                return (bool)(logic_t)arg;
            else if constexpr (std::is_same_v<T, real_t>)
                return (bool)arg;
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return (bool)arg;
            else
                return false;
        },
        value);
}

bool ConstantValue::isFalse() const {
    return std::visit(
        [](auto&& arg) noexcept {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, SVInt>) {
                logic_t l = (logic_t)arg;
                return !l.isUnknown() && l.value == 0;
            }
            else if constexpr (std::is_same_v<T, real_t>)
                return !(bool)arg;
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return !(bool)arg;
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return true;
            else
                return false;
        },
        value);
}

bool ConstantValue::hasUnknown() const {
    return std::visit(
        [](auto&& arg) noexcept {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, SVInt>) {
                return arg.hasUnknown();
            }
            else if constexpr (std::is_same_v<T, Elements>) {
                for (auto& element : arg) {
                    if (element.hasUnknown())
                        return true;
                }
                return false;
            }
            else if constexpr (std::is_same_v<T, Map>) {
                for (auto& [key, val] : *arg) {
                    if (key.hasUnknown() || val.hasUnknown())
                        return true;
                }
                return false;
            }
            else if constexpr (std::is_same_v<T, Queue>) {
                for (auto& element : *arg) {
                    if (element.hasUnknown())
                        return true;
                }
                return false;
            }
            else {
                return false;
            }
        },
        value);
}

ConstantValue ConstantValue::convertToInt(bitwidth_t width, bool isSigned, bool isFourState) const {
    if (isReal())
        return SVInt::fromDouble(width, real(), isSigned);

    if (isShortReal())
        return SVInt::fromFloat(width, shortReal(), isSigned);

    if (!isInteger())
        return nullptr;

    SVInt result = integer();
    if (!isFourState)
        result.flattenUnknowns();

    // [11.8.3] says that during an assignment we sign extend iff the rhs is signed.
    // That means we should resize first, and only then change the sign flag if desired.
    if (width != result.getBitWidth())
        result = result.resize(width);

    result.setSigned(isSigned);
    return result;
}

ConstantValue ConstantValue::convertToReal() const {
    if (isReal())
        return *this;

    if (isShortReal())
        return real_t(shortReal());

    if (isInteger())
        return real_t(integer().toDouble());

    return nullptr;
}

ConstantValue ConstantValue::convertToShortReal() const {
    if (isShortReal())
        return *this;

    if (isReal())
        return shortreal_t((float)real());

    if (isInteger())
        return shortreal_t(integer().toFloat());

    return nullptr;
}

ConstantValue ConstantValue::convertToStr() const {
    if (isString())
        return *this;

    if (!isInteger())
        return nullptr;

    // Conversion is described in [6.16]: take each 8 bit chunk,
    // remove it if it's zero, otherwise add as character to the string.
    // TODO: unknown bits?

    const SVInt& val = integer();
    int32_t msb = int32_t(val.getBitWidth() - 1);
    int32_t extraBits = int32_t(val.getBitWidth() % 8);

    std::string result;
    if (extraBits) {
        auto c = val.slice(msb, msb - extraBits + 1).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= extraBits;
    }

    while (msb >= 7) {
        auto c = val.slice(msb, msb - 7).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= 8;
    }

    return result;
}

std::ostream& operator<<(std::ostream& os, const ConstantValue& cv) {
    return os << cv.toString();
}

bool operator==(const ConstantValue& lhs, const ConstantValue& rhs) {
    return std::visit(
        [&](auto&& arg) noexcept(
            !std::is_same_v<std::decay_t<decltype(arg)>, ConstantValue::Elements>) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return rhs.bad();
            else if constexpr (std::is_same_v<T, SVInt>)
                return rhs.isInteger() && exactlyEqual(arg, rhs.integer());
            else if constexpr (std::is_same_v<T, real_t>)
                return rhs.isReal() && arg == double(rhs.real());
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return rhs.isShortReal() && arg == float(rhs.shortReal());
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return rhs.isNullHandle();
            else if constexpr (std::is_same_v<T, ConstantValue::Elements>) {
                if (!rhs.isUnpacked())
                    return false;

                return arg == std::get<ConstantValue::Elements>(rhs.value);
            }
            else if constexpr (std::is_same_v<T, std::string>)
                return rhs.isString() && arg == rhs.str();
            else if constexpr (std::is_same_v<T, ConstantValue::Map>) {
                if (!rhs.isMap())
                    return false;

                return *arg == *rhs.map();
            }
            else if constexpr (std::is_same_v<T, ConstantValue::Queue>) {
                if (!rhs.isQueue())
                    return false;

                return *arg == *rhs.queue();
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        lhs.value);
}

bool operator<(const ConstantValue& lhs, const ConstantValue& rhs) {
    return std::visit(
        [&](auto&& arg) noexcept(
            !std::is_same_v<std::decay_t<decltype(arg)>, ConstantValue::Elements>) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return false;
            else if constexpr (std::is_same_v<T, SVInt>)
                return rhs.isInteger() && bool(arg < rhs.integer());
            else if constexpr (std::is_same_v<T, real_t>)
                return rhs.isReal() && arg < double(rhs.real());
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return rhs.isShortReal() && arg < float(rhs.shortReal());
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return false;
            else if constexpr (std::is_same_v<T, ConstantValue::Elements>) {
                if (!rhs.isUnpacked())
                    return false;

                return arg < std::get<ConstantValue::Elements>(rhs.value);
            }
            else if constexpr (std::is_same_v<T, std::string>)
                return rhs.isString() && arg < rhs.str();
            else if constexpr (std::is_same_v<T, ConstantValue::Map>) {
                if (!rhs.isMap())
                    return false;

                return *arg < *rhs.map();
            }
            else if constexpr (std::is_same_v<T, ConstantValue::Queue>) {
                if (!rhs.isQueue())
                    return false;

                return *arg < *rhs.queue();
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        lhs.value);
}

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

int32_t ConstantRange::translateIndex(int32_t index) const {
    if (!isLittleEndian())
        return upper() - index;
    else
        return index - lower();
}

bool ConstantRange::containsPoint(int32_t index) const {
    return index >= lower() && index <= upper();
}

std::string ConstantRange::toString() const {
    return fmt::format("[{}:{}]", left, right);
}

std::ostream& operator<<(std::ostream& os, const ConstantRange& cr) {
    return os << cr.toString();
}

} // namespace slang
