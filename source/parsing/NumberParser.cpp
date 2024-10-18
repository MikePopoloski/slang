//------------------------------------------------------------------------------
// NumberParser.cpp
// Helper type to construct numeric tokens
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/NumberParser.h"

#include "slang/diagnostics/LexerDiags.h"
#include "slang/text/CharInfo.h"
#include "slang/util/String.h"

namespace slang::parsing {

static logic_t getLogicCharValue(char c) {
    switch (c) {
        case 'z':
        case 'Z':
        case '?':
            return logic_t::z;
        case 'x':
        case 'X':
            return logic_t::x;
        default:
            return logic_t(0);
    }
}

NumberParser::NumberParser(Diagnostics& diagnostics, BumpAllocator& alloc,
                           LanguageVersion languageVersion) :
    languageVersion(languageVersion), diagnostics(diagnostics), alloc(alloc) {
}

void NumberParser::startVector(Token baseToken, Token sizeToken) {
    hasUnknown = false;
    valid = true;
    digits.clear();
    text.clear();

    NumericTokenFlags baseFlags = baseToken.numericFlags();
    literalBase = baseFlags.base();
    signFlag = baseFlags.isSigned();

    // Diagnose errors where they only provided a sign and no base.
    if (auto baseRaw = baseToken.rawText(); baseRaw.length() == 2 && ::tolower(baseRaw[1]) == 's')
        addDiag(diag::ExpectedIntegerBaseAfterSigned, baseToken.location() + 1);

    sizeBits = 0;
    if (sizeToken) {
        const SVInt& sizeVal = sizeToken.intValue();
        if (sizeVal == 0) {
            addDiag(diag::LiteralSizeIsZero, sizeToken.location());
        }
        else if (sizeVal > (int)SVInt::MAX_BITS) {
            sizeBits = SVInt::MAX_BITS;
            addDiag(diag::LiteralSizeTooLarge, sizeToken.location()) << (int)SVInt::MAX_BITS;
        }
        else {
            sizeBits = sizeVal.as<bitwidth_t>().value();
        }
    }
}

int NumberParser::append(Token token, bool isFirst) {
    text.append_range(token.rawText());

    // If we've had an error thus far, don't bother doing anything else that
    // might just add more errors on the pile.
    if (!valid)
        return -1;

    // set valid to false since we return early when we encounter errors
    // if we're still good at the end of the function we'll flip this back
    valid = false;

    // underscore as the first char is not allowed
    std::string_view chars = token.rawText();
    SourceLocation location = token.location();
    if (isFirst && chars.length() && chars[0] == '_') {
        addDiag(diag::DigitsLeadingUnderscore, location);
        return -1;
    }

    int index = 0;
    switch (literalBase) {
        case LiteralBase::Binary:
            for (char c : chars) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 2);
                else if (isBinaryDigit(c))
                    addDigit(logic_t(getDigitValue(c)), 2);
                else if (c != '_') {
                    addDiag(diag::BadBinaryDigit, location + index);
                    return -1;
                }
                index++;
            }
            break;
        case LiteralBase::Octal:
            for (char c : chars) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 8);
                else if (isOctalDigit(c))
                    addDigit(logic_t(getDigitValue(c)), 8);
                else if (c != '_') {
                    addDiag(diag::BadOctalDigit, location + index);
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
            if (isFirst) {
                if (chars.length() == 1 && isLogicDigit(chars[0])) {
                    addDigit(getLogicCharValue(chars[0]), 10);
                    break;
                }

                if (token.kind == TokenKind::IntegerLiteral) {
                    decimalValue = token.intValue();
                    break;
                }
            }

            // As mentioned above, this loop is just for checking errors.
            for (char c : chars) {
                if (isLogicDigit(c) || isDecimalDigit(c)) {
                    if (hasUnknown) {
                        addDiag(diag::DecimalDigitMultipleUnknown, location + index);
                        return -1;
                    }

                    hasUnknown = isLogicDigit(c);
                }
                else if (c != '_') {
                    addDiag(diag::BadDecimalDigit, location + index);
                    return -1;
                }
                index++;
            }
            break;
        case LiteralBase::Hex:
            for (char c : chars) {
                if (isLogicDigit(c))
                    addDigit(getLogicCharValue(c), 16);
                else if (isHexDigit(c))
                    addDigit(logic_t(getHexDigitValue(c)), 16);
                else if (c == '+' || c == '-') {
                    // This is ok, this was initially lexed as a real token with exponent.
                    // Slice off everything after and including the operator, which will
                    // become new tokens.
                    text.resize(text.size() - (chars.size() - size_t(index)));
                    valid = true;
                    return index;
                }
                else if (c != '_') {
                    addDiag(diag::BadHexDigit, location + index);
                    return -1;
                }
                index++;
            }
            break;
        default:
            SLANG_UNREACHABLE;
    }

    valid = true;
    return -1;
}

Token NumberParser::finishValue(Token firstToken, bool singleToken, bool isNegated) {
    auto createResult = [&](auto&& val) {
        return Token(alloc, TokenKind::IntegerLiteral, firstToken.trivia(),
                     singleToken ? firstToken.rawText() : toStringView(text.copy(alloc)),
                     firstLocation, std::forward<decltype(val)>(val));
    };

    auto checkOverflow = [&](bitwidth_t computedWidth, const SVInt& value) {
        // Special case to avoid the warning when we have a minus operator preceeding
        // a min value signed negative integer, with no unknowns.
        if (isNegated && signFlag && !hasUnknown && computedWidth == sizeBits + 1 &&
            value.isNegative() && value.countOnes() == 1) {
            return;
        }

        addDiag(diag::VectorLiteralOverflow, firstLocation) << computedWidth;
    };

    if (!valid)
        return createResult(0);

    if (literalBase == LiteralBase::Decimal && !hasUnknown) {
        // If we added an x or z, we will fall through to the general handler below.
        // Otherwise, optimize for this case by reusing the integer value already
        // computed by the token itself.
        bitwidth_t width = decimalValue.getBitWidth();
        if (signFlag) {
            width++;
            decimalValue = decimalValue.resize(width);
        }

        // If no size was specified, just return the value as-is. Otherwise,
        // resize it to match the desired size. Warn if that will truncate.
        SVInt result;
        if (!sizeBits) {
            // Unsized numbers are required to be at least 32 bits by the spec.
            if (width < 32)
                result = decimalValue.resize(32);
            else
                result = std::move(decimalValue);
        }
        else if (width != sizeBits) {
            result = decimalValue.resize(sizeBits);
            if (width > sizeBits)
                checkOverflow(width, result);
        }
        else {
            result = std::move(decimalValue);
        }

        result.setSigned(signFlag);
        return createResult(std::move(result));
    }

    if (digits.empty()) {
        digits.push_back(logic_t(0));
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
                SLANG_UNREACHABLE;
        }

        // All of the digits in the number require `multiplier` bits, except for
        // possibly the first (leading) digit. This one has leading zeros in it,
        // so only requires clog2(d+1) bits.
        bitwidth_t bits = 0;
        if (digits.size() > 1)
            bits = bitwidth_t(digits.size() - 1) * multiplier;

        // If the leading digit is unknown however, allow any size.
        if (!digits[0].isUnknown())
            bits += (bitwidth_t)std::bit_width(digits[0].value);

        if (bits > sizeBits) {
            if (sizeBits == 0) {
                if (bits > SVInt::MAX_BITS) {
                    bits = SVInt::MAX_BITS;
                    addDiag(diag::LiteralSizeTooLarge, firstLocation) << (int)SVInt::MAX_BITS;
                }

                sizeBits = std::max(32u, bits);
            }
            else {
                auto result = SVInt::fromDigits(sizeBits, literalBase, signFlag, hasUnknown,
                                                digits);
                checkOverflow(bits, result);
                return createResult(std::move(result));
            }
        }
    }

    return createResult(
        SVInt::fromDigits(sizeBits ? sizeBits : 32, literalBase, signFlag, hasUnknown, digits));
}

void NumberParser::addDigit(logic_t digit, int maxValue) {
    // Leading zeros obviously don't count towards our bit limit, so
    // only count them if we've seen other non-zero digits
    if (digit.isUnknown()) {
        // Keep one leading zero, if any, for msb extension
        hasUnknown = true;
    }
    else {
        SLANG_ASSERT(digit.value < maxValue);
        if (digits.size() == 1 && digits.front().value == 0) {
            if (digit.value == 0)
                return; // at most one leading zero

            // If first nonzero not unknown, no leading zeros
            digits.pop_back();
        }
    }
    digits.push_back(digit);
}

Diagnostic& NumberParser::addDiag(DiagCode code, SourceLocation location) {
    return diagnostics.add(code, location);
}

NumberParser::IntResult NumberParser::reportMissingDigits(Token sizeToken, Token baseToken,
                                                          Token first) {
    // If we issued this error in response to seeing an EOF token, back up and put
    // the error on the last consumed token instead.
    SourceLocation errLoc;
    if (first && first.kind != TokenKind::EndOfFile)
        errLoc = first.location();
    else
        errLoc = baseToken.location() + baseToken.rawText().size();

    addDiag(diag::ExpectedVectorDigits, errLoc);
    return IntResult::vector(sizeToken, baseToken,
                             Token::createMissing(alloc, TokenKind::IntegerLiteral, errLoc));
}

void NumberParser::reportIntOverflow(Token token) {
    SVInt val = token.intValue().resize(32);
    val.setSigned(true);

    addDiag(diag::SignedIntegerOverflow, token.location()) << val;
}

} // namespace slang::parsing
