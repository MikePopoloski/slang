#include "BitVector.h"

#include "Diagnostics.h"

namespace slang {

const logic_t logic_t::x = 1 << 7;
const logic_t logic_t::z = 1 << 6;

VectorBuilder::VectorBuilder(BumpAllocator& alloc, Diagnostics& diagnostics) :
    alloc(alloc), diagnostics(diagnostics)
{
}

void VectorBuilder::start() {
    hasUnknown = false;
    digits.clear();
}

void VectorBuilder::addBinaryDigit(logic_t digit) {
    commonAddDigit(digit, 2);
}

void VectorBuilder::addOctalDigit(logic_t digit) {
    commonAddDigit(digit, 8);
}

void VectorBuilder::addDecimalDigit(logic_t digit) {
    commonAddDigit(digit, 10);
}

void VectorBuilder::addHexDigit(logic_t digit) {
    commonAddDigit(digit, 16);
}

LogicVector VectorBuilder::finish(LiteralBase base, uint32_t size, SourceLocation location) {
    // figure out how much space we actually need for our digits
    ASSERT(digits.count(), "No digits somehow?");
    switch (base) {
        case LiteralBase::Binary: {
            uint32_t bits = digits.count();
            if (bits > size)
                diagnostics.add(DiagCode::TooManyLiteralDigits, location);

            if (hasUnknown || bits > 64)
                return LogicVector(size, digits.copy(alloc));

            return LogicVector(size, calcBinary());
        }
        case LiteralBase::Octal: {
            uint32_t bits = digits.count() * 3;
            if (bits > size)
                diagnostics.add(DiagCode::TooManyLiteralDigits, location);

            if (hasUnknown || bits > 64)
                return LogicVector(size, digits.copy(alloc));

            return LogicVector(size, calcOctal());
        }
        case LiteralBase::Hex: {
            uint32_t bits = digits.count() * 4;
            if (bits > size)
                diagnostics.add(DiagCode::TooManyLiteralDigits, location);

            if (hasUnknown || bits > 64)
                return LogicVector(size, digits.copy(alloc));

            return LogicVector(size, calcHex());
        }
        case LiteralBase::Decimal: {
            if (hasUnknown)
                return LogicVector(size, digits.copy(alloc));

            uint64_t value = calcDecimal(location);
            uint32_t bits = (uint32_t)std::ceil(std::log2(value));
            if (bits > size)
                diagnostics.add(DiagCode::TooManyLiteralDigits, location);

            return LogicVector(size, value);
        }
        default:
            ASSERT(false, "Unknown base");
    }
    // unreachable
    return LogicVector(0, 0);
}

void VectorBuilder::commonAddDigit(logic_t digit, int maxValue) {
    digits.append(digit);
    if (digit.isUnknown())
        hasUnknown = true;
    else {
        ASSERT(digit.value < maxValue);
    }
}

uint64_t VectorBuilder::calcBinary() const {
    int i = 0;
    uint64_t value = 0;
    for (logic_t d : digits) {
        value |= d.value << i;
        i++;
    }
    return value;
}

uint64_t VectorBuilder::calcOctal() const {
    uint64_t value = 0;
    for (logic_t d : digits) {
        value *= 8;
        value += d.value;
    }
    return value;
}

uint64_t VectorBuilder::calcHex() const {
    uint64_t value = 0;
    for (logic_t d : digits) {
        value *= 16;
        value += d.value;
    }
    return value;
}

uint64_t VectorBuilder::calcDecimal(SourceLocation location) const {
    uint64_t value = 0;
    for (logic_t d : digits) {
        value *= 10;
        value += d.value;
        if (value > UINT32_MAX) {
            diagnostics.add(DiagCode::DecimalLiteralOverflow, location);
            break;
        }
    }
    return value;
}

}