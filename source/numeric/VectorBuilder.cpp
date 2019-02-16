//------------------------------------------------------------------------------
// VectorBuilder.cpp
// Helper type to construct SVInt instances.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/numeric/VectorBuilder.h"

#include "../text/CharInfo.h"

#include "slang/diagnostics/Diagnostics.h"

namespace slang {

VectorBuilder::VectorBuilder(Diagnostics& diagnostics) : diagnostics(diagnostics) {
}

void VectorBuilder::start(LiteralBase base, bitwidth_t size, bool isSigned,
                          SourceLocation location) {
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
    string_view text = token.rawText();
    SourceLocation location = token.location();
    if (first && text.length() && text[0] == '_') {
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
                if (isLogicDigit(c) || isDecimalDigit(c)) {
                    if (hasUnknown) {
                        diagnostics.add(DiagCode::DecimalDigitMultipleUnknown, location + index);
                        return;
                    }

                    if (isLogicDigit(c))
                        addDigit(getLogicCharValue(text[0]), 10);
                    else
                        addDigit(logic_t(getDigitValue(c)), 10);
                }
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
            THROW_UNREACHABLE;
    }

    first = false;
    valid = true;
}

SVInt VectorBuilder::finish() {
    if (!valid)
        return 0;

    if (digits.empty())
        digits.append(logic_t(0));
    else if (literalBase == LiteralBase::Decimal) {
        if (!hasUnknown) {
            uint64_t value = 0;
            for (logic_t d : digits) {
                value *= 10;
                value += d.value;
                if (value > UINT32_MAX) {
                    diagnostics.add(DiagCode::DecimalLiteralOverflow, firstLocation);
                    return 0;
                }
            }
        }
    }
    else {
        uint32_t multiplier = 0;
        switch (literalBase) {
            case LiteralBase::Binary:
                multiplier = 1;
                break;
            case LiteralBase::Octal:
                multiplier = 3;
                break;
            case LiteralBase::Hex:
                multiplier = 4;
                break;
            default:
                THROW_UNREACHABLE;
        }
        // All of the digits in the number require `multiplier` bits, except for
        // possibly the first (leading) digit. This one has leading zeros in it,
        // so only requires clog2(d+1) bits. If the leading digit is unknown
        // however, we go with the default multiplier amount.
        bitwidth_t bits = 0;
        if (digits.size() > 1)
            bits = (digits.size() - 1) * multiplier;

        if (digits[0].isUnknown())
            bits += multiplier;
        else
            bits += clog2(digits[0].value + 1);

        if (bits > sizeBits) {
            if (sizeBits == 0) {
                if (bits > SVInt::MAX_BITS) {
                    diagnostics.add(DiagCode::VectorLiteralOverflow, firstLocation);
                    bits = SVInt::MAX_BITS;
                }

                return SVInt::fromDigits(std::max(32u, bits), literalBase, signFlag, hasUnknown,
                                         digits);
            }
            else {
                // we should warn about overflow here, but the spec says it is valid and
                // the literal gets truncated. Definitely a warning though.
                diagnostics.add(DiagCode::VectorLiteralOverflow, firstLocation);
            }
        }
    }

    return SVInt::fromDigits(sizeBits ? sizeBits : 32, literalBase, signFlag, hasUnknown, digits);
}

void VectorBuilder::addDigit(logic_t digit, int maxValue) {
    // Leading zeros obviously don't count towards our bit limit, so
    // only count them if we've seen other non-zero digits
    if (digit.value != 0 || digits.size() != 0) {
        digits.append(digit);
        if (digit.isUnknown())
            hasUnknown = true;
        else
            ASSERT(digit.value < maxValue);
    }
}

} // namespace slang
