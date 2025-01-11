//------------------------------------------------------------------------------
// ConstantValue.cpp
// Compile-time constant representation
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/numeric/ConstantValue.h"

#include <ostream>

#include "slang/numeric/MathUtils.h"
#include "slang/text/FormatBuffer.h"
#include "slang/util/Hash.h"

namespace slang {

template<typename T>
struct always_false : std::false_type {};

const ConstantValue ConstantValue::Invalid;

std::string ConstantValue::toString(bitwidth_t abbreviateThresholdBits, bool exactUnknowns,
                                    bool useAssignmentPatterns) const {
    return std::visit(
        [abbreviateThresholdBits, exactUnknowns, useAssignmentPatterns](auto&& arg) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return "<unset>"s;
            else if constexpr (std::is_same_v<T, SVInt>)
                return arg.toString(abbreviateThresholdBits, exactUnknowns);
            else if constexpr (std::is_same_v<T, real_t>)
                return fmt::format("{}", double(arg));
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return fmt::format("{}", float(arg));
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return "null"s;
            else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                return "$"s;
            else if constexpr (std::is_same_v<T, Elements>) {
                FormatBuffer buffer;
                buffer.append(useAssignmentPatterns ? "'{"sv : "["sv);
                for (auto& element : arg) {
                    buffer.append(element.toString(abbreviateThresholdBits, exactUnknowns,
                                                   useAssignmentPatterns));
                    buffer.append(",");
                }

                if (!arg.empty())
                    buffer.pop_back();
                buffer.append(useAssignmentPatterns ? "}"sv : "]"sv);
                return buffer.str();
            }
            else if constexpr (std::is_same_v<T, std::string>)
                return fmt::format("\"{}\"", arg);
            else if constexpr (std::is_same_v<T, Map>) {
                FormatBuffer buffer;
                buffer.append(useAssignmentPatterns ? "'{"sv : "["sv);
                for (auto& [key, val] : *arg)
                    buffer.format("{}:{},",
                                  key.toString(abbreviateThresholdBits, exactUnknowns,
                                               useAssignmentPatterns),
                                  val.toString(abbreviateThresholdBits, exactUnknowns,
                                               useAssignmentPatterns));

                if (arg->defaultValue)
                    buffer.format("default:{}",
                                  arg->defaultValue.toString(abbreviateThresholdBits, exactUnknowns,
                                                             useAssignmentPatterns));
                else if (!arg->empty())
                    buffer.pop_back();

                buffer.append(useAssignmentPatterns ? "}"sv : "]"sv);
                return buffer.str();
            }
            else if constexpr (std::is_same_v<T, Queue>) {
                FormatBuffer buffer;
                buffer.append(useAssignmentPatterns ? "'{"sv : "["sv);
                for (auto& element : *arg) {
                    buffer.append(element.toString(abbreviateThresholdBits, exactUnknowns,
                                                   useAssignmentPatterns));
                    buffer.append(",");
                }

                if (!arg->empty())
                    buffer.pop_back();
                buffer.append(useAssignmentPatterns ? "}"sv : "]"sv);
                return buffer.str();
            }
            else if constexpr (std::is_same_v<T, Union>) {
                if (!arg->activeMember)
                    return "(unset)"s;

                return fmt::format("({}) {}", *arg->activeMember,
                                   arg->value.toString(abbreviateThresholdBits, exactUnknowns,
                                                       useAssignmentPatterns));
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
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
                hash_combine(h, slang::hash<double>()(arg));
            else if constexpr (std::is_same_v<T, shortreal_t>)
                hash_combine(h, slang::hash<float>()(arg));
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                hash_combine(h, 0);
            else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                hash_combine(h, '$');
            else if constexpr (std::is_same_v<T, Elements>) {
                for (auto& element : arg)
                    hash_combine(h, element.hash());
            }
            else if constexpr (std::is_same_v<T, std::string>)
                hash_combine(h, slang::hash<std::string>()(arg));
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
            else if constexpr (std::is_same_v<T, Union>) {
                if (!arg->activeMember)
                    hash_combine(h, 1);
                else {
                    hash_combine(h, 3);
                    hash_combine(h, arg->value.hash());
                }
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        value);
    return h;
}

bool ConstantValue::empty() const {
    return size() == 0;
}

size_t ConstantValue::size() const {
    return std::visit(
        [](auto&& arg) noexcept {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, Elements>)
                return arg.size();
            else if constexpr (std::is_same_v<T, Map>)
                return arg->size();
            else if constexpr (std::is_same_v<T, Queue>)
                return arg->size();
            else if constexpr (std::is_same_v<T, std::string>)
                return arg.size();
            else
                return size_t(0);
        },
        value);
}

ConstantValue& ConstantValue::at(size_t index) {
    return std::visit(
        [index](auto&& arg) -> ConstantValue& {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, Elements>)
                return arg.at(index);
            else if constexpr (std::is_same_v<T, Queue>)
                return arg->at(index);
            else
                SLANG_UNREACHABLE;
        },
        value);
}

const ConstantValue& ConstantValue::at(size_t index) const {
    return std::visit(
        [index](auto&& arg) -> const ConstantValue& {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, Elements>)
                return arg.at(index);
            else if constexpr (std::is_same_v<T, Queue>)
                return arg->at(index);
            else
                SLANG_UNREACHABLE;
        },
        value);
}

ConstantValue ConstantValue::getSlice(int32_t upper, int32_t lower,
                                      const ConstantValue& defaultValue) const {
    if (isInteger())
        return integer().slice(upper, lower);

    if (isUnpacked()) {
        std::span<const ConstantValue> elems = elements();
        std::vector<ConstantValue> result{size_t(upper - lower + 1)};
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
            if (i >= 0 && size_t(i) < q.size())
                result.push_back(q[size_t(i)]);
        }

        return result;
    }

    if (isString()) {
        SLANG_ASSERT(upper == lower);
        SLANG_ASSERT(upper >= 0);
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
            else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                return true;
            else if constexpr (std::is_same_v<T, std::string>)
                return !arg.empty();
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
            else if constexpr (std::is_same_v<T, std::string>)
                return arg.empty();
            else
                return false;
        },
        value);
}

bool ConstantValue::hasUnknown() const {
    return std::visit(
        [](auto&& arg) {
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

ConstantValue ConstantValue::convertToInt() const {
    if (isReal())
        return convertToInt(64, true, false);
    if (isShortReal())
        return convertToInt(32, true, false);
    if (isString()) {
        bitwidth_t bits = bitwidth_t(str().length() * 8);
        if (!bits)
            bits = 8;

        return convertToInt(bits, false, false);
    }
    if (!isInteger())
        return nullptr;

    return *this;
}

ConstantValue ConstantValue::convertToInt(bitwidth_t width, bool isSigned, bool isFourState) const {
    if (isReal())
        return SVInt::fromDouble(width, real(), isSigned);

    if (isShortReal())
        return SVInt::fromFloat(width, shortReal(), isSigned);

    if (isString()) {
        SmallVector<byte, 8> buffer;
        auto& s = str();
        for (auto it = s.rbegin(); it != s.rend(); it++)
            buffer.push_back(static_cast<byte>(*it));

        SVInt result(width, buffer, isSigned);
        if (!isFourState)
            result.flattenUnknowns();

        return result;
    }

    if (isUnbounded())
        return *this;

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

    const SVInt& val = integer();
    int32_t msb = int32_t(val.getBitWidth() - 1);
    int32_t extraBits = int32_t(val.getBitWidth() % 8);

    std::string result;
    result.reserve((val.getBitWidth() + 7) / 8);
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

ConstantValue ConstantValue::convertToByteArray(bitwidth_t size, bool isSigned) const {
    if (isUnpacked())
        return *this;

    std::string result;
    if (isInteger())
        result = convertToStr().str();
    else if (isString())
        result = str();
    else
        return nullptr;

    if (!size) // dynamic array use string size
        size = static_cast<bitwidth_t>(result.size());

    Elements array;
    array.reserve(size);

    for (auto ch : result) {
        if (array.size() >= size)
            break;
        array.emplace_back(SVInt(8, static_cast<uint64_t>(ch), isSigned));
    }

    while (array.size() < size)
        array.emplace_back(SVInt(8, 0, isSigned));
    return array;
}

ConstantValue ConstantValue::convertToByteQueue(bool isSigned) const {
    if (isQueue())
        return *this;

    std::string result;
    if (isInteger())
        result = convertToStr().str();
    else if (isString())
        result = str();
    else
        return nullptr;

    SVQueue queue;
    for (auto ch : result)
        queue.emplace_back(SVInt(8, static_cast<uint64_t>(ch), isSigned));

    return queue;
}

uint64_t ConstantValue::getBitstreamWidth() const {
    // Note that we don't have to worry about overflow in this
    // method because we have an artificial limit on how
    // large constant values are allowed to be.
    // TODO: actually implement the mentioned limit
    if (isInteger())
        return integer().getBitWidth();

    if (isString())
        return str().length() * CHAR_BIT;

    uint64_t width = 0;
    if (isUnpacked()) {
        for (const auto& cv : elements())
            width += cv.getBitstreamWidth();
    }
    else if (isMap()) {
        for (const auto& kv : *map())
            width += kv.second.getBitstreamWidth();
    }
    else if (isQueue()) {
        for (const auto& cv : *queue())
            width += cv.getBitstreamWidth();
    }
    else if (isUnion()) {
        width = unionVal()->value.getBitstreamWidth();
    }

    return width;
}

std::optional<bitwidth_t> ConstantValue::getEffectiveWidth() const {
    if (!isInteger())
        return std::nullopt;

    auto& sv = integer();
    if (sv.hasUnknown())
        return sv.getBitWidth();

    if (sv.isNegative())
        return sv.getMinRepresentedBits();

    return sv.getActiveBits();
}

std::ostream& operator<<(std::ostream& os, const ConstantValue& cv) {
    return os << cv.toString();
}

bool operator==(const ConstantValue& lhs, const ConstantValue& rhs) {
    return std::visit(
        [&](auto&& arg) {
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
            else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                return rhs.isUnbounded();
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
            else if constexpr (std::is_same_v<T, ConstantValue::Union>) {
                if (!rhs.isUnion())
                    return false;

                auto& ru = rhs.unionVal();
                return arg->activeMember == ru->activeMember && arg->value == ru->value;
            }
            else {
                static_assert(always_false<T>::value, "Missing case");
            }
        },
        lhs.value);
}

std::partial_ordering operator<=>(const ConstantValue& lhs, const ConstantValue& rhs) {
    return std::visit(
        [&](auto&& arg) -> std::partial_ordering {
            constexpr auto unordered = std::partial_ordering::unordered;
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return unordered;
            else if constexpr (std::is_same_v<T, SVInt>) {
                if (!rhs.isInteger())
                    return unordered;

                auto& rhi = rhs.integer();
                if (arg < rhi)
                    return std::partial_ordering::less;
                else if (arg == rhi)
                    return std::partial_ordering::equivalent;
                else
                    return std::partial_ordering::greater;
            }
            else if constexpr (std::is_same_v<T, real_t>)
                return rhs.isReal() ? arg <=> double(rhs.real()) : unordered;
            else if constexpr (std::is_same_v<T, shortreal_t>)
                return rhs.isShortReal() ? arg <=> float(rhs.shortReal()) : unordered;
            else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                return unordered;
            else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                return unordered;
            else if constexpr (std::is_same_v<T, ConstantValue::Elements>) {
                if (!rhs.isUnpacked())
                    return unordered;

                return arg <=> std::get<ConstantValue::Elements>(rhs.value);
            }
            else if constexpr (std::is_same_v<T, std::string>) {
                if (!rhs.isString())
                    return unordered;

                return arg <=> rhs.str();
            }
            else if constexpr (std::is_same_v<T, ConstantValue::Map>) {
                if (!rhs.isMap())
                    return unordered;

                return *arg <=> *rhs.map();
            }
            else if constexpr (std::is_same_v<T, ConstantValue::Queue>) {
                if (!rhs.isQueue())
                    return unordered;

                return *arg <=> *rhs.queue();
            }
            else if constexpr (std::is_same_v<T, ConstantValue::Union>) {
                if (!rhs.isUnion())
                    return unordered;

                return *arg <=> *rhs.unionVal();
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

    SLANG_ASSERT(result.right <= upper());
    if (isLittleEndian())
        return result;
    else
        return result.reverse();
}

ConstantRange ConstantRange::intersect(ConstantRange other) const {
    if (overlaps(other)) {
        ConstantRange result;
        result.left = std::max(lower(), other.lower());
        result.right = std::min(upper(), other.upper());
        return result;
    }
    return ConstantRange();
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

bool ConstantRange::contains(ConstantRange other) const {
    return other.lower() >= lower() && other.upper() <= upper();
}

bool ConstantRange::overlaps(ConstantRange other) const {
    return lower() <= other.upper() && upper() >= other.lower();
}

std::optional<ConstantRange> ConstantRange::getIndexedRange(int32_t l, int32_t r, bool littleEndian,
                                                            bool indexedUp) {
    ConstantRange result;
    int32_t count = r - 1;
    if (indexedUp) {
        auto upper = checkedAddS32(l, count);
        if (!upper)
            return std::nullopt;

        result.left = *upper;
        result.right = l;
    }
    else {
        auto lower = checkedSubS32(l, count);
        if (!lower)
            return std::nullopt;

        result.left = l;
        result.right = *lower;
    }

    if (!littleEndian)
        return result.reverse();

    return result;
}

std::string ConstantRange::toString() const {
    return fmt::format("[{}:{}]", left, right);
}

std::ostream& operator<<(std::ostream& os, const ConstantRange& cr) {
    return os << cr.toString();
}

} // namespace slang
