//------------------------------------------------------------------------------
//! @file NumberParser.h
//! @brief Helper type to parse numeric literals
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cmath>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/numeric/SVInt.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"

namespace slang::parsing {

class NumberParser {
public:
    NumberParser(Diagnostics& diagnostics, BumpAllocator& alloc);

    struct IntResult {
        Token size;
        Token base;
        Token value;
        bool isSimple = true;

        static IntResult simple(Token value) { return {Token(), Token(), value, true}; }

        static IntResult vector(Token size, Token base, Token value) {
            return {size, base, value, false};
        }
    };

    template<typename TStream>
    IntResult parseSimpleInt(TStream& stream) {
        auto token = stream.expect(TokenKind::IntegerLiteral);
        if (token.intValue() > INT32_MAX)
            reportIntOverflow(token);
        return IntResult::simple(token);
    }

    template<typename TStream, bool RequireSameLine = false>
    IntResult parseInteger(TStream& stream) {
        Token sizeToken;
        Token baseToken;

        auto token = stream.consume();
        if (token.kind == TokenKind::IntegerBase) {
            baseToken = token;
            startVector(baseToken, Token());
        }
        else {
            auto createSimple = [&] {
                if (token.intValue() > INT32_MAX)
                    reportIntOverflow(token);
                return IntResult::simple(token);
            };

            if constexpr (RequireSameLine) {
                if (!stream.peekSameLine())
                    return createSimple();
            }

            if (!stream.peek(TokenKind::IntegerBase))
                return createSimple();

            sizeToken = token;
            baseToken = stream.consume();
            startVector(baseToken, sizeToken);
        }

        if constexpr (RequireSameLine) {
            if (!stream.peekSameLine())
                return reportMissingDigits(sizeToken, baseToken, Token());
        }

        // At this point we expect to see vector digits, but they could be split out into other
        // token types because of hex literals.
        auto first = stream.peek();
        if (!syntax::SyntaxFacts::isPossibleVectorDigit(first.kind))
            return reportMissingDigits(sizeToken, baseToken, first);

        int count = 0;
        Token next = first;
        firstLocation = first.location();

        do {
            count++;
            int index = append(next, count == 1);
            stream.consume();

            if (index >= 0) {
                // This handles a really obnoxious case: 'h 3e+2
                // The second token is initially lexed as a real literal, but we need to split
                // it apart here now that we know it's a hex literal and put the remaining (new)
                // tokens back on the parser's stack.
                stream.handleExponentSplit(next, (size_t)index);

                // Bump the count so that we definitely take the modified raw text
                // instead of trying to use the initial token's raw directly.
                count++;
                break;
            }

            if constexpr (RequireSameLine) {
                if (!stream.peekSameLine())
                    break;
            }

            next = stream.peek();
        } while (syntax::SyntaxFacts::isPossibleVectorDigit(next.kind) && next.trivia().empty());

        return IntResult::vector(sizeToken, baseToken, finishValue(first, count == 1));
    }

    template<typename TStream>
    Token parseReal(TStream& stream) {
        // have to check for overflow here, now that we know this is actually a real
        auto literal = stream.consume();
        if (literal.numericFlags().outOfRange()) {
            if (literal.realValue() == 0) {
                addDiag(diag::RealLiteralUnderflow, literal.location())
                    << real_t(std::numeric_limits<double>::denorm_min());
            }
            else {
                SLANG_ASSERT(!std::isfinite(literal.realValue()));
                addDiag(diag::RealLiteralOverflow, literal.location())
                    << real_t(std::numeric_limits<double>::max());
            }
        }
        return literal;
    }

private:
    void startVector(Token baseToken, Token sizeToken);
    int append(Token token, bool isFirst);
    Token finishValue(Token firstToken, bool singleToken);
    void addDigit(logic_t digit, int maxValue);
    Diagnostic& addDiag(DiagCode code, SourceLocation location);
    IntResult reportMissingDigits(Token sizeToken, Token baseToken, Token first);
    void reportIntOverflow(Token token);

    bitwidth_t sizeBits = 0;
    LiteralBase literalBase = LiteralBase::Binary;
    SourceLocation firstLocation;
    bool signFlag = false;
    bool hasUnknown = false;
    bool valid = false;
    SVInt decimalValue;
    Diagnostics& diagnostics;
    BumpAllocator& alloc;
    SmallVector<logic_t> digits;
    SmallVector<char> text;
};

} // namespace slang::parsing
