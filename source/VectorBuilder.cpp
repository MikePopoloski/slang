#include "VectorBuilder.h"

#include "CharInfo.h"
#include "Diagnostics.h"

namespace slang {

VectorBuilder::VectorBuilder(BumpAllocator& alloc, Diagnostics& diagnostics) :
    alloc(alloc), diagnostics(diagnostics)
{
}

void VectorBuilder::start(LiteralBase base, uint16_t size, bool isSigned, SourceLocation location) {
    literalBase = base;
    sizeBits = size;
    firstLocation = location;

    signFlag = isSigned;
    hasUnknown = false;
    valid = true;
    first = true;
    digits.clear();
}

void VectorBuilder::append(Token token) {
    // If we've had an error thus far, don't bother doing anything else that
    // might just add more errors on the pile.
    if (!valid)
        return;

    // set valid to false since we return early when we encounter errors
    // if we're still good at the end of the function we'll flip this back
    valid = false;

    // underscore as the first char is not allowed
    StringRef text = token.rawText();
    if (text.length() == 0)
        return;

    SourceLocation location = token.location();
    if (first && text[0] == '_') {
        diagnostics.add(DiagCode::VectorDigitsLeadingUnderscore, location);
        return;
    }

    int index = 0;
    switch (literalBase) {
        case LiteralBase::Binary:
            for (char c : text) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 2);
                else if (isBinaryDigit(c))
                    addDigit(logic_t(getDigitValue(c)), 2);
                else if (c != '_') {
                    diagnostics.add(DiagCode::BadBinaryDigit, location + index);
                    return;
                }
                index++;
            }
            break;
        case LiteralBase::Octal:
            for (char c : text) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 8);
                else if (isOctalDigit(c))
                    addDigit(logic_t(getDigitValue(c)), 8);
                else if (c != '_') {
                    diagnostics.add(DiagCode::BadOctalDigit, location + index);
                    return;
                }
                index++;
            }
            break;
        case LiteralBase::Decimal:
            // in decimal literals you can only use x or z if it's the only digit 
            if (first && text.length() == 1 && isLogicDigit(text[0])) {
                addDigit(getLogicCharValue(text[0]), 10);
                break;
            }

            for (char c : text) {
                if (isLogicDigit(c)) {
                    diagnostics.add(DiagCode::DecimalDigitMultipleUnknown, location + index);
                    return;
                }
                else if (isDecimalDigit(c))
                    addDigit(logic_t(getDigitValue(c)), 10);
                else if (c != '_') {
                    diagnostics.add(DiagCode::BadDecimalDigit, location + index);
                    return;
                }
                index++;
            }
            break;
        case LiteralBase::Hex:
            for (char c : text) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 16);
                else if (isHexDigit(c))
                    addDigit(logic_t(getHexDigitValue(c)), 16);
                else if (c != '_') {
                    diagnostics.add(DiagCode::BadHexDigit, location + index);
                    return;
                }
                index++;
            }
            break;
        default:
            ASSERT(false, "Impossible");
    }

    first = false;
    valid = true;
}

SVInt VectorBuilder::finish() {
    // figure out how much space we actually need for our digits
    ASSERT(digits.count(), "No digits somehow?");

    // do some error checking on the bit size
    switch (literalBase) {
        case LiteralBase::Binary:
            if (digits.count() > sizeBits) {
                diagnostics.add(DiagCode::VectorLiteralOverflow, firstLocation);
                return SVInt(0);
            }
            break;
        case LiteralBase::Octal:
            if (digits.count() * 3 > sizeBits) {
                diagnostics.add(DiagCode::VectorLiteralOverflow, firstLocation);
                return SVInt(0);
            }
            break;
        case LiteralBase::Hex:
            if (digits.count() * 4 > sizeBits) {
                diagnostics.add(DiagCode::VectorLiteralOverflow, firstLocation);
                return SVInt(0);
            }
            break;
        case LiteralBase::Decimal:
            if (!hasUnknown) {
                uint64_t value = 0;
                for (logic_t d : digits) {
                    value *= 10;
                    value += d.value;
                    if (value > UINT32_MAX) {
                        diagnostics.add(DiagCode::DecimalLiteralOverflow, firstLocation);
                        return SVInt(0);
                    }
                }
            }
            break;
        default:
            ASSERT(false, "Unknown base");
    }

    return SVInt(sizeBits, literalBase, signFlag, hasUnknown, ArrayRef<logic_t>(digits.begin(), digits.count()));
}

void VectorBuilder::addDigit(logic_t digit, int maxValue) {
    digits.append(digit);
    if (digit.isUnknown())
        hasUnknown = true;
    else
        ASSERT(digit.value < maxValue);
}

}