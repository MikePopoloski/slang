#include "BitVector.h"

#include "Diagnostics.h"

#include "SVInt.h"

namespace {

uint32_t clog2(uint64_t value) {
	return (uint32_t)std::ceil(std::log(value));
}

}

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
	if (hasUnknown)
		// TODO: check overflow and other junk once we have arbitrary precision lib
		return LogicVector(size, digits.copy(alloc));

    switch (base) {
        case LiteralBase::Binary: {
			uint64_t value = calcBinary();
			checkSize(value, size, location);
            return LogicVector(size, value);
        }
        case LiteralBase::Octal: {
			uint64_t value = calcOctal();
			checkSize(value, size, location);
            return LogicVector(size, value);
        }
        case LiteralBase::Hex: {
			uint64_t value = calcHex();
			checkSize(value, size, location);
            return LogicVector(size, calcHex());
        }
        case LiteralBase::Decimal: {
            uint64_t value = calcDecimal(location);
			checkSize(value, size, location);
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

void VectorBuilder::checkSize(uint64_t value, uint32_t size, SourceLocation location) {
	if (clog2(value) > size)
		diagnostics.add(DiagCode::VectorLiteralOverflow, location);
}

uint64_t VectorBuilder::calcBinary() const {
    uint64_t value = 0;
    for (logic_t d : digits) {
		value *= 2;
		value += d.value;
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