//------------------------------------------------------------------------------
// VectorBuilder.cpp
// Helper type to construct SVInt instances.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/numeric/VectorBuilder.h"

#include "../text/CharInfo.h"

#include "slang/diagnostics/LexerDiags.h"
#include "slang/diagnostics/NumericDiags.h"

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

int VectorBuilder::append(Token token) {
    // If we've had an error thus far, don't bother doing anything else that
    // might just add more errors on the pile.
    if (!valid)
        return -1;

    // set valid to false since we return early when we encounter errors
    // if we're still good at the end of the function we'll flip this back
    valid = false;

    // underscore as the first char is not allowed
    string_view text = token.rawText();
    SourceLocation location = token.location();
    if (first && text.length() && text[0] == '_') {
        diagnostics.add(diag::DigitsLeadingUnderscore, location);
        return -1;
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
                    diagnostics.add(diag::BadBinaryDigit, location + index);
                    return -1;
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
                    diagnostics.add(diag::BadOctalDigit, location + index);
                    return -1;
                }
                index++;
            }
            break;
        case LiteralBase::Decimal:
            // Decimals have the restriction that you can only use x or z if it's the only digit.
            // Further, they can obviously only have decimal numbers (not A-F letters). Combined,
            // this means that we should only ever see one token here in practice, unless there's
            // an error. Optimize for this case and just suck the decimal value that's already
            // been computed out of the token itself.
            if (first) {
                if (text.length() == 1 && isLogicDigit(text[0])) {
                    addDigit(getLogicCharValue(text[0]), 10);
                    break;
                }

                if (token.kind == TokenKind::IntegerLiteral) {
                    decimalValue = token.intValue();
                    break;
                }
            }

            // As mentioned above, this loop is just for checking errors.
            for (char c : text) {
                if (isLogicDigit(c) || isDecimalDigit(c)) {
                    if (hasUnknown) {
                        diagnostics.add(diag::DecimalDigitMultipleUnknown, location + index);
                        return -1;
                    }

                    hasUnknown = isLogicDigit(c);
                }
                else if (c != '_') {
                    diagnostics.add(diag::BadDecimalDigit, location + index);
                    return -1;
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
                else if (c == '+' || c == '-') {
                    // This is ok, this was initially lexed as a real token with exponent.
                    first = false;
                    valid = true;
                    return index;
                }
                else if (c != '_') {
                    diagnostics.add(diag::BadHexDigit, location + index);
                    return -1;
                }
                index++;
            }
            break;
        default:
            THROW_UNREACHABLE;
    }

    first = false;
    valid = true;
    return -1;
}

SVInt VectorBuilder::finish() {
    if (!valid)
        return 0;

    if (literalBase == LiteralBase::Decimal) {
        // If we added an x or z, fall through to the general handler below.
        // Otherwise, optimize for this case by reusing the integer value already
        // computed by the token itself.
        if (!hasUnknown) {
            // If no size was specified, just return the value as-is. Otherwise,
            // resize it to match the desired size. Warn if that will truncate.
            bitwidth_t width = decimalValue.getBitWidth();
            SVInt result;
            if (!sizeBits) {
                // Unsized numbers are required to be at least 32 bits by the spec.
                if (width < 32)
                    result = decimalValue.resize(32);
                else
                    result = std::move(decimalValue);
            }
            else if (width != sizeBits) {
                if (width > sizeBits)
                    diagnostics.add(diag::VectorLiteralOverflow, firstLocation);

                result = decimalValue.resize(sizeBits);
            }
            else {
                result = std::move(decimalValue);
            }

            result.setSigned(signFlag);
            return result;
        }
    }

    if (digits.empty()) {
        digits.append(logic_t(0));
    }
    else if (literalBase != LiteralBase::Decimal) {
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
            bits = bitwidth_t(digits.size() - 1) * multiplier;

        if (digits[0].isUnknown())
            bits += multiplier;
        else
            bits += clog2(digits[0].value + 1);

        if (bits > sizeBits) {
            if (sizeBits == 0) {
                if (bits > SVInt::MAX_BITS) {
                    bits = SVInt::MAX_BITS;
                    diagnostics.add(diag::LiteralSizeTooLarge, firstLocation)
                        << (int)SVInt::MAX_BITS;
                }

                sizeBits = std::max(32u, bits);
            }
            else {
                // We should warn about overflow here, but the spec says it is valid and
                // the literal gets truncated. Definitely a warning though.
                diagnostics.add(diag::VectorLiteralOverflow, firstLocation);
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
