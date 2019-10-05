//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/ConstantValue.h"

#include <fmt/format.h>
#include <nlohmann/json.hpp>

#include "slang/text/FormatBuffer.h"

namespace slang {

const ConstantValue ConstantValue::Invalid;

std::string ConstantValue::toString() const {
    return std::visit([](auto&& arg) noexcept {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, std::monostate>)
            return "<unset>"s;
        else if constexpr (std::is_same_v<T, SVInt>)
            return arg.toString();
        else if constexpr (std::is_same_v<T, real_t>)
            return std::to_string(arg);
        else if constexpr (std::is_same_v<T, shortreal_t>)
            return std::to_string(arg);
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
        else
            static_assert(always_false<T>::value, "Missing case");
    },
                      value);
}

ConstantValue ConstantValue::getSlice(int32_t upper, int32_t lower) const {
    if (isInteger())
        return integer().slice(upper, lower);

    if (isUnpacked()) {
        auto slice = elements().subspan(lower, upper - lower + 1);
        return std::vector<ConstantValue>(slice.begin(), slice.end());
    }

    if (isString()) {
        ASSERT(upper == lower);
        ASSERT(upper >= 0);
        return SVInt(8, (uint64_t)str()[uint64_t(upper)], false);
    }

    return nullptr;
}

bool ConstantValue::isTrue() const {
    return std::visit([](auto&& arg) noexcept {
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
    return std::visit([](auto&& arg) noexcept {
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

bool ConstantValue::equivalentTo(const ConstantValue& rhs) const {
    return std::visit(
        [&](auto&& arg) noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Elements>) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return false;
            else if constexpr (std::is_same_v<T, SVInt>)
                return rhs.isInteger() && exactlyEqual(arg, rhs.integer());
            else if constexpr (std::is_same_v<T, real_t>)
                return rhs.isReal() && arg == rhs.real();
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return rhs.isShortReal() && arg == rhs.shortReal();
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return rhs.isNullHandle();
            else if constexpr (std::is_same_v<T, Elements>) {
                if (!rhs.isUnpacked())
                    return false;

                auto rhsElements = rhs.elements();
                if (arg.size() != (size_t)rhsElements.size())
                    return false;

                for (size_t i = 0; i < arg.size(); i++) {
                    if (!arg[i].equivalentTo(rhsElements[ptrdiff_t(i)]))
                        return false;
                }

                return true;
            }
            else if constexpr (std::is_same_v<T, std::string>)
                return rhs.isString() && arg == rhs.str();
            else
                static_assert(always_false<T>::value, "Missing case");
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

void to_json(json& j, const ConstantValue& cv) {
    j = cv.toString();
}

std::ostream& operator<<(std::ostream& os, const ConstantValue& cv) {
    return os << cv.toString();
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

ConstantValue LValue::load() const {
    return std::visit([](auto&& arg) noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat>)
                          ->ConstantValue {
                              using T = std::decay_t<decltype(arg)>;
                              if constexpr (std::is_same_v<T, std::monostate>)
                                  return ConstantValue();
                              else if constexpr (std::is_same_v<T, ConstantValue*>)
                                  return *arg;
                              else if constexpr (std::is_same_v<T, CVRange>)
                                  return arg.cv->getSlice(arg.range.upper(), arg.range.lower());
                              else if constexpr (std::is_same_v<T, Concat>) {
                                  SmallVectorSized<SVInt, 4> vals;
                                  for (auto& elem : arg)
                                      vals.append(elem.load().integer());
                                  return SVInt::concat(vals);
                              }
                              else
                                  static_assert(always_false<T>::value, "Missing case");
                          },
                      value);
}

void LValue::store(const ConstantValue& newValue) {
    std::visit(
        [&newValue](auto&& arg) noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat> &&
                                         !std::is_same_v<std::decay_t<decltype(arg)>, CVRange>) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>) {
                return;
            }
            else if constexpr (std::is_same_v<T, ConstantValue*>) {
                *arg = newValue;
            }
            else if constexpr (std::is_same_v<T, CVRange>) {
                ConstantValue& cv = *arg.cv;
                ASSERT(cv);

                int32_t l = arg.range.lower();
                int32_t u = arg.range.upper();

                if (cv.isUnpacked()) {
                    auto src = newValue.elements();
                    auto dest = cv.elements();

                    for (int32_t i = l; i <= u; i++)
                        dest[i] = src[i - l];
                }
                else if (cv.isString()) {
                    ASSERT(l == u);
                    ASSERT(l >= 0);
                    char c = (char)*newValue.integer().as<uint8_t>();
                    if (c)
                        cv.str()[uint64_t(l)] = c;
                }
                else {
                    cv.integer().set(u, l, newValue.integer());
                }
            }
            else if constexpr (std::is_same_v<T, Concat>) {
                auto& sv = newValue.integer();
                int32_t msb = (int32_t)sv.getBitWidth() - 1;

                for (auto& elem : arg) {
                    int32_t width = (int32_t)elem.load().integer().getBitWidth();
                    elem.store(sv.slice(msb, msb - width + 1));
                    msb -= width;
                }
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        value);
}

LValue LValue::selectRange(ConstantRange range) const {
    return std::visit(
        [&range](auto&& arg) noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat>)
            ->LValue {
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
            },
        value);
}

LValue LValue::selectIndex(int32_t index) const {
    return std::visit(
        [index](auto&& arg) noexcept(!std::is_same_v<std::decay_t<decltype(arg)>, Concat>)->LValue {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return nullptr;
            else if constexpr (std::is_same_v<T, ConstantValue*>)
                return LValue(arg->elements()[index]);
            else if constexpr (std::is_same_v<T, CVRange>)
                return LValue(arg.cv->elements()[arg.range.lower() + index]);
            else if constexpr (std::is_same_v<T, Concat>)
                THROW_UNREACHABLE;
            else
                static_assert(always_false<T>::value, "Missing case");
        },
        value);
}

} // namespace slang
