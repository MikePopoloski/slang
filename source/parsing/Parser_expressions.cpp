//------------------------------------------------------------------------------
// Parser_expressions.cpp
// Expression-related parsing methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

namespace slang {

ExpressionSyntax& Parser::parseExpression() {
    return parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
}

ExpressionSyntax& Parser::parseMinTypMaxExpression() {
    ExpressionSyntax& first = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto& typ = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
    auto colon2 = expect(TokenKind::Colon);
    auto& max = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);

    return factory.minTypMaxExpression(first, colon1, typ, colon2, max);
}

ExpressionSyntax& Parser::parseSubExpression(bitmask<ExpressionOptions> options, int precedence) {
    auto dg = setDepthGuard();

    auto current = peek();
    if (current.kind == TokenKind::NewKeyword)
        return parseNewExpression(nullptr);
    else if (isPossibleDelayOrEventControl(current.kind)) {
        auto timingControl = parseTimingControl();
        ASSERT(timingControl);

        auto& expr = factory.timingControlExpression(*timingControl, parseExpression());
        return parsePostfixExpression(expr);
    }
    else if (current.kind == TokenKind::TaggedKeyword) {
        // TODO: check for trailing expression
        auto tagged = consume();
        auto member = expect(TokenKind::Identifier);
        return factory.taggedUnionExpression(tagged, member, nullptr);
    }

    ExpressionSyntax* leftOperand;
    SyntaxKind opKind = getUnaryPrefixExpression(current.kind);
    if (opKind != SyntaxKind::Unknown)
        leftOperand = &parsePrefixExpression(options, opKind);
    else
        leftOperand = &parsePrimaryExpression();

    while (true) {
        // either a binary operator, or we're done
        current = peek();
        opKind = getBinaryExpression(current.kind);
        if (opKind == SyntaxKind::Unknown)
            break;

        // the "or" operator in event expressions is special, we don't handle it here
        if (opKind == SyntaxKind::OrSequenceExpression &&
            (options & ExpressionOptions::EventExpressionContext)) {
            break;
        }

        // we have to special case '<=', which can be less than or nonblocking assignment depending
        // on context
        if (opKind == SyntaxKind::LessThanEqualExpression &&
            (options & ExpressionOptions::ProceduralAssignmentContext)) {

            options &= ~ExpressionOptions::ProceduralAssignmentContext;
            opKind = SyntaxKind::NonblockingAssignmentExpression;
        }

        // see if we should take this operator or if it's part of our parent due to precedence
        int newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        if (opKind == SyntaxKind::InsideExpression)
            leftOperand = &parseInsideExpression(*leftOperand);
        else {
            auto opToken = consume();
            auto attributes = parseAttributes();
            auto& rightOperand = parseSubExpression(options, newPrecedence);
            leftOperand =
                &factory.binaryExpression(opKind, *leftOperand, opToken, attributes, rightOperand);
        }
    }

    // can't nest pattern matching expressions
    if (options & ExpressionOptions::AllowPatternMatch) {
        // if we see the matches keyword or &&& we're in a pattern conditional predicate
        // if we see a question mark, we were in a simple conditional predicate (at the precedence
        // level one beneath logical-or)
        auto logicalOrPrecedence = getPrecedence(SyntaxKind::LogicalOrExpression);
        if (current.kind == TokenKind::MatchesKeyword || current.kind == TokenKind::TripleAnd ||
            (current.kind == TokenKind::Question && precedence < logicalOrPrecedence)) {

            Token question;
            auto& predicate =
                parseConditionalPredicate(*leftOperand, TokenKind::Question, question);
            auto attributes = parseAttributes();
            auto& left = parseSubExpression(options, logicalOrPrecedence - 1);
            auto colon = expect(TokenKind::Colon);
            auto& right = parseSubExpression(options, logicalOrPrecedence - 1);
            leftOperand =
                &factory.conditionalExpression(predicate, question, attributes, left, colon, right);
        }
    }
    return *leftOperand;
}

ExpressionSyntax& Parser::parsePrefixExpression(bitmask<ExpressionOptions> options,
                                                SyntaxKind opKind) {
    switch (opKind) {
        case SyntaxKind::UnarySequenceDelayExpression:
        case SyntaxKind::UnarySequenceEventExpression: {
            auto timing = parseTimingControl();
            ASSERT(timing);
            return factory.timingControlExpression(*timing, parseExpression());
        }
        case SyntaxKind::NextTimePropertyExpression:
        case SyntaxKind::SNextTimePropertyExpression:
        case SyntaxKind::AlwaysPropertyExpression:
        case SyntaxKind::SAlwaysPropertyExpression:
        case SyntaxKind::EventuallyPropertyExpression:
        case SyntaxKind::SEventuallyPropertyExpression:
            // TODO:
            break;
        case SyntaxKind::AcceptOnPropertyExpression:
        case SyntaxKind::RejectOnPropertyExpression:
        case SyntaxKind::SyncAcceptOnPropertyExpression:
        case SyntaxKind::SyncRejectOnPropertyExpression:
            // TODO:
            break;
        default:
            break;
    }

    auto opToken = consume();
    auto attributes = parseAttributes();

    ExpressionSyntax& operand = parseSubExpression(options, getPrecedence(opKind));
    return factory.prefixUnaryExpression(opKind, opToken, attributes, operand);
}

ExpressionSyntax& Parser::parsePrimaryExpression() {
    ExpressionSyntax* expr;
    TokenKind kind = peek().kind;
    switch (kind) {
        case TokenKind::StringLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::NullKeyword:
        case TokenKind::OneStep:
        case TokenKind::Dollar: {
            auto literal = consume();
            expr = &factory.literalExpression(getLiteralExpression(literal.kind), literal);
            break;
        }
        case TokenKind::RealLiteral: {
            // have to check for overflow here, now that we know this is actually a real
            auto literal = consume();
            if (literal.numericFlags().outOfRange()) {
                if (literal.realValue() == 0) {
                    addDiag(diag::RealLiteralUnderflow, literal.location())
                        << real_t(std::numeric_limits<double>::denorm_min());
                }
                else {
                    ASSERT(!std::isfinite(literal.realValue()));
                    addDiag(diag::RealLiteralOverflow, literal.location())
                        << real_t(std::numeric_limits<double>::max());
                }
            }

            expr = &factory.literalExpression(SyntaxKind::RealLiteralExpression, literal);
            break;
        }
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
            expr = &parseIntegerExpression();
            break;
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            expr = &parseMinTypMaxExpression();

            auto closeParen = expect(TokenKind::CloseParenthesis);
            expr = &factory.parenthesizedExpression(openParen, *expr, closeParen);
            break;
        }
        case TokenKind::ApostropheOpenBrace:
            return parseAssignmentPatternExpression(nullptr);
        case TokenKind::OpenBrace: {
            // several different things this could be:
            // 1. empty queue expression { }
            // 2. streaming concatenation {>> {expr}}
            // 3. multiple concatenation {expr {concat}}
            // 4. concatenation {expr, expr}
            auto openBrace = consume();
            switch (peek().kind) {
                case TokenKind::CloseBrace:
                    expr = &factory.emptyQueueExpression(openBrace, consume());
                    break;
                case TokenKind::LeftShift:
                case TokenKind::RightShift:
                    expr = &parseStreamConcatenation(openBrace);
                    break;
                default: {
                    auto& first = parseExpression();
                    if (!peek(TokenKind::OpenBrace))
                        expr = &parseConcatenation(openBrace, &first);
                    else {
                        auto openBraceInner = consume();
                        auto& concat = parseConcatenation(openBraceInner, nullptr);
                        auto closeBrace = expect(TokenKind::CloseBrace);
                        expr = &factory.multipleConcatenationExpression(openBrace, first, concat,
                                                                        closeBrace);
                    }
                    break;
                }
            }
            break;
        }
        case TokenKind::SignedKeyword:
        case TokenKind::UnsignedKeyword: {
            auto signing = consume();
            auto apostrophe = expect(TokenKind::Apostrophe);
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& innerExpr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& parenExpr = factory.parenthesizedExpression(openParen, innerExpr, closeParen);
            expr = &factory.signedCastExpression(signing, apostrophe, parenExpr);
            break;
        }
        default:
            // possibilities here:
            // 1. data type
            // 2. qualified name
            // 3. implicit class handles
            // 4. any of [1-3] with an assignment pattern
            // 5. any of [1-3] with a cast expression
            // 6. error
            if (isPossibleDataType(kind) && kind != TokenKind::Identifier &&
                kind != TokenKind::UnitSystemName) {

                auto& type = parseDataType(/* allowImplicit */ false);
                if (peek(TokenKind::ApostropheOpenBrace))
                    expr = &parseAssignmentPatternExpression(&type);
                else
                    expr = &type;
            }
            else {
                // parseName() will insert a missing identifier token for the error case
                auto& name = parseName(NameOptions::ExpectingExpression);
                if (peek(TokenKind::ApostropheOpenBrace))
                    expr = &parseAssignmentPatternExpression(&factory.namedType(name));
                else {
                    // otherwise just a name expression
                    expr = &name;
                }
            }
            break;
    }
    return parsePostfixExpression(*expr);
}

ExpressionSyntax& Parser::parseIntegerExpression() {
    Token sizeToken;
    Token baseToken;
    bitwidth_t sizeBits = 0;

    auto token = consume();
    if (token.kind == TokenKind::IntegerBase)
        baseToken = token;
    else {
        const SVInt& tokenValue = token.intValue();
        if (!peek(TokenKind::IntegerBase)) {
            if (tokenValue > INT32_MAX)
                addDiag(diag::SignedIntegerOverflow, token.location());
            return factory.literalExpression(SyntaxKind::IntegerLiteralExpression, token);
        }

        sizeToken = token;
        baseToken = consume();

        if (tokenValue == 0) {
            addDiag(diag::LiteralSizeIsZero, token.location());
        }
        else if (tokenValue > SVInt::MAX_BITS) {
            sizeBits = SVInt::MAX_BITS;
            addDiag(diag::LiteralSizeTooLarge, token.location()) << (int)SVInt::MAX_BITS;
        }
        else {
            sizeBits = tokenValue.as<bitwidth_t>().value();
        }
    }

    // at this point we expect to see vector digits, but they could be split out into other token
    // types because of hex literals
    auto first = peek();
    if (!isPossibleVectorDigit(first.kind)) {
        addDiag(diag::ExpectedVectorDigits, first.location());
        return factory.integerVectorExpression(
            sizeToken, baseToken, missingToken(TokenKind::IntegerLiteral, first.location()));
    }

    Token next = first;
    NumericTokenFlags baseFlags = baseToken.numericFlags();
    SmallVectorSized<char, 64> text;
    int count = 0;

    vectorBuilder.start(baseFlags.base(), sizeBits, baseFlags.isSigned(), first.location());
    do {
        count++;
        text.appendRange(next.rawText());
        consume();

        int index = vectorBuilder.append(next);
        if (index >= 0) {
            // This handles a really obnoxious case: 'h 3e+2
            // The second token is initially lexed as a real literal, but we need to split
            // it apart here now that we know it's a hex literal and put the remaining (new)
            // tokens back on the parser's stack.
            handleExponentSplit(next, (size_t)index);
            break;
        }

        next = peek();
    } while (isPossibleVectorDigit(next.kind) && next.trivia().empty());

    string_view rawText = count == 1 ? first.rawText() : to_string_view(text.copy(alloc));

    Token valToken = Token::create(alloc, TokenKind::IntegerLiteral, first.trivia(), rawText,
                                   first.location(), vectorBuilder.finish());

    return factory.integerVectorExpression(sizeToken, baseToken, valToken);
}

void Parser::handleExponentSplit(Token token, size_t offset) {
    SmallVectorSized<Token, 4> split;
    Lexer::splitTokens(alloc, getDiagnostics(), getPP().getSourceManager(), token, offset,
                       getPP().getCurrentKeywordVersion(), split);

    pushTokens(split);
}

ExpressionSyntax& Parser::parseInsideExpression(ExpressionSyntax& expr) {
    auto inside = expect(TokenKind::InsideKeyword);
    auto& list = parseOpenRangeList();
    return factory.insideExpression(expr, inside, list);
}

OpenRangeListSyntax& Parser::parseOpenRangeList() {
    Token openBrace;
    Token closeBrace;
    span<TokenOrSyntax> list;

    parseSeparatedList<isPossibleOpenRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBrace, list, closeBrace,
        diag::ExpectedOpenRangeElement, [this] { return &parseOpenRangeElement(); });

    return factory.openRangeList(openBrace, list, closeBrace);
}

ExpressionSyntax& Parser::parseOpenRangeElement() {
    if (!peek(TokenKind::OpenBracket))
        return parseExpression();
    return parseElementSelect();
}

ConcatenationExpressionSyntax& Parser::parseConcatenation(Token openBrace,
                                                          ExpressionSyntax* first) {
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    if (first) {
        // it's possible to have just one element in the concatenation list, so check for a close
        // brace
        buffer.append(first);
        if (peek(TokenKind::CloseBrace))
            return factory.concatenationExpression(openBrace, buffer.copy(alloc), consume());

        buffer.append(expect(TokenKind::Comma));
    }

    Token closeBrace;
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, diag::ExpectedExpression,
        [this] { return &parseExpression(); });
    return factory.concatenationExpression(openBrace, buffer.copy(alloc), closeBrace);
}

StreamingConcatenationExpressionSyntax& Parser::parseStreamConcatenation(Token openBrace) {
    auto op = consume();
    ExpressionSyntax* sliceSize = nullptr;
    if (!peek(TokenKind::OpenBrace))
        sliceSize = &parseExpression();

    Token openBraceInner;
    Token closeBraceInner;
    span<TokenOrSyntax> list;

    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBraceInner, list,
        closeBraceInner, diag::ExpectedStreamExpression,
        [this] { return &parseStreamExpression(); });

    auto closeBrace = expect(TokenKind::CloseBrace);
    return factory.streamingConcatenationExpression(openBrace, op, sliceSize, openBraceInner, list,
                                                    closeBraceInner, closeBrace);
}

StreamExpressionSyntax& Parser::parseStreamExpression() {
    auto& expr = parseExpression();

    StreamExpressionWithRangeSyntax* withRange = nullptr;
    if (peek(TokenKind::WithKeyword)) {
        auto with = consume();
        withRange = &factory.streamExpressionWithRange(with, parseElementSelect());
    }

    return factory.streamExpression(expr, withRange);
}

AssignmentPatternExpressionSyntax& Parser::parseAssignmentPatternExpression(DataTypeSyntax* type) {
    auto openBrace = expect(TokenKind::ApostropheOpenBrace);

    // we either have an expression here, or the default keyword for a pattern key
    ExpressionSyntax* firstExpr;
    if (peek(TokenKind::DefaultKeyword))
        firstExpr = &factory.literalExpression(SyntaxKind::DefaultPatternKeyExpression, consume());
    else
        firstExpr = &parseExpression();

    Token closeBrace;
    AssignmentPatternSyntax* pattern;
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    switch (peek().kind) {
        case TokenKind::Colon:
            buffer.append(&parseAssignmentPatternItem(firstExpr));
            parseSeparatedList<isPossibleExpressionOrCommaOrDefault, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace,
                diag::ExpectedAssignmentKey,
                [this] { return &parseAssignmentPatternItem(nullptr); });
            pattern =
                &factory.structuredAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
        case TokenKind::OpenBrace: {
            auto innerOpenBrace = consume();
            parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.replicatedAssignmentPattern(openBrace, *firstExpr, innerOpenBrace,
                                                           buffer.copy(alloc), closeBrace,
                                                           expect(TokenKind::CloseBrace));
            break;
        }
        case TokenKind::Comma:
            buffer.append(firstExpr);
            buffer.append(consume());
            parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.simpleAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
        default:
            buffer.append(firstExpr);
            parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.simpleAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
    }
    ASSERT(pattern);
    return factory.assignmentPatternExpression(type, *pattern);
}

AssignmentPatternItemSyntax& Parser::parseAssignmentPatternItem(ExpressionSyntax* key) {
    if (!key)
        key = &parseExpression();

    auto colon = expect(TokenKind::Colon);
    return factory.assignmentPatternItem(*key, colon, parseExpression());
}

ElementSelectSyntax& Parser::parseElementSelect() {
    auto openBracket = expect(TokenKind::OpenBracket);
    auto selector = parseElementSelector();
    auto closeBracket = expect(TokenKind::CloseBracket);
    return factory.elementSelect(openBracket, selector, closeBracket);
}

SelectorSyntax* Parser::parseElementSelector() {
    if (peek().kind == TokenKind::CloseBracket) {
        return nullptr;
    }
    auto& expr = parseExpression();
    switch (peek().kind) {
        case TokenKind::Colon: {
            auto range = consume();
            return &factory.rangeSelect(SyntaxKind::SimpleRangeSelect, expr, range,
                                        parseExpression());
        }
        case TokenKind::PlusColon: {
            auto range = consume();
            return &factory.rangeSelect(SyntaxKind::AscendingRangeSelect, expr, range,
                                        parseExpression());
        }
        case TokenKind::MinusColon: {
            auto range = consume();
            return &factory.rangeSelect(SyntaxKind::DescendingRangeSelect, expr, range,
                                        parseExpression());
        }
        default:
            return &factory.bitSelect(expr);
    }
}

ExpressionSyntax& Parser::parsePostfixExpression(ExpressionSyntax& lhs) {
    ExpressionSyntax* expr = &lhs;
    while (true) {
        switch (peek().kind) {
            case TokenKind::OpenBracket:
                expr = &factory.elementSelectExpression(*expr, parseElementSelect());
                break;
            case TokenKind::Dot: {
                auto dot = consume();
                auto name = expect(TokenKind::Identifier);
                expr = &factory.memberAccessExpression(*expr, dot, name);
                break;
            }
            case TokenKind::OpenParenthesis:
                expr = &factory.invocationExpression(*expr, nullptr, &parseArgumentList());
                break;
            case TokenKind::DoublePlus:
            case TokenKind::DoubleMinus: {
                // can't have any other postfix expressions after inc/dec
                auto op = consume();
                return factory.postfixUnaryExpression(getUnaryPostfixExpression(op.kind), *expr,
                                                      nullptr, op);
            }
            case TokenKind::Apostrophe: {
                auto apostrophe = consume();
                auto openParen = expect(TokenKind::OpenParenthesis);
                auto& innerExpr = parseExpression();
                auto closeParen = expect(TokenKind::CloseParenthesis);
                auto& parenExpr = factory.parenthesizedExpression(openParen, innerExpr, closeParen);
                expr = &factory.castExpression(*expr, apostrophe, parenExpr);
                break;
            }
            case TokenKind::OpenParenthesisStar: {
                auto attributes = parseAttributes();
                switch (peek().kind) {
                    case TokenKind::DoublePlus:
                    case TokenKind::DoubleMinus: {
                        auto op = consume();
                        return factory.postfixUnaryExpression(getUnaryPostfixExpression(op.kind),
                                                              *expr, attributes, op);
                    }
                    case TokenKind::OpenParenthesis:
                        expr =
                            &factory.invocationExpression(*expr, attributes, &parseArgumentList());
                        break;
                    default:
                        // otherwise, this has to be a function call without any arguments
                        expr = &factory.invocationExpression(*expr, attributes, nullptr);
                        break;
                }
                break;
            }
            case TokenKind::WithKeyword:
                // If we see bracket right after the with keyword, this is actually part of a stream
                // expression return and let the call further up the stack handle it.
                if (peek(1).kind == TokenKind::OpenBracket)
                    return *expr;
                expr = &parseArrayOrRandomizeWithClause();
                break;
            case TokenKind::NewKeyword:
                expr = &parseNewExpression(expr);
                break;
            case TokenKind::DoubleHash: {
                auto timing = parseTimingControl();
                ASSERT(timing);
                expr = &factory.timingControlExpressionConcatenation(*expr, *timing,
                                                                     parseExpression());
                break;
            }
            default:
                return *expr;
        }
    }
}

NameSyntax& Parser::parseName() {
    return parseName(NameOptions::None);
}

NameSyntax& Parser::parseName(bitmask<NameOptions> options) {
    NameSyntax* name = &parseNamePart(options | NameOptions::IsFirst);
    options &= ~NameOptions::ExpectingExpression;

    bool usedDot = false;
    bool reportedError = false;
    SyntaxKind previousKind = name->kind;

    auto kind = peek().kind;
    while (kind == TokenKind::Dot || kind == TokenKind::DoubleColon) {
        auto separator = consume();
        if (kind == TokenKind::Dot)
            usedDot = true;
        else if (usedDot && !reportedError) {
            reportedError = true;
            addDiag(diag::InvalidAccessDotColon, separator.location()) << "::"sv
                                                                       << "."sv;
        }
        else if (peek().kind == TokenKind::NewKeyword)
            return factory.classScope(*name, separator);

        switch (previousKind) {
            case SyntaxKind::UnitScope:
            case SyntaxKind::LocalScope:
                if (kind != TokenKind::DoubleColon) {
                    addDiag(diag::InvalidAccessDotColon, separator.location()) << "."sv
                                                                               << "::"sv;
                }
                break;
            case SyntaxKind::RootScope:
            case SyntaxKind::ThisHandle:
            case SyntaxKind::SuperHandle:
                if (kind != TokenKind::Dot) {
                    addDiag(diag::InvalidAccessDotColon, separator.location()) << "::"sv
                                                                               << "."sv;
                }
                break;
            default:
                break;
        }

        bitmask<NameOptions> nextOptions = options;
        if (previousKind == SyntaxKind::ThisHandle)
            nextOptions |= NameOptions::PreviousWasThis;

        NameSyntax& rhs = parseNamePart(nextOptions);
        previousKind = rhs.kind;

        name = &factory.scopedName(*name, separator, rhs);
        kind = peek().kind;
    }

    // If we saw $unit, $root, super, or local, make sure the correct token follows it.
    TokenKind expectedKind = TokenKind::Unknown;
    switch (name->kind) {
        case SyntaxKind::UnitScope:
        case SyntaxKind::LocalScope:
            expectedKind = TokenKind::DoubleColon;
            break;
        case SyntaxKind::RootScope:
        case SyntaxKind::SuperHandle:
            expectedKind = TokenKind::Dot;
            break;
        default:
            break;
    }

    if (expectedKind != TokenKind::Unknown) {
        auto separator = expect(expectedKind);
        name = &factory.scopedName(*name, separator, parseNamePart(options));
    }

    return *name;
}

NameSyntax& Parser::parseNamePart(bitmask<NameOptions> options) {
    auto kind = getKeywordNameExpression(peek().kind);
    if (kind != SyntaxKind::Unknown) {
        bool isFirst = (options & NameOptions::IsFirst) != 0;
        if ((isFirst != isSpecialMethodName(kind)) ||
            (kind == SyntaxKind::SuperHandle && (options & NameOptions::PreviousWasThis))) {
            return factory.keywordName(kind, consume());
        }
    }

    TokenKind next = peek().kind;
    bool inForEach = (options & NameOptions::InForEach) != 0;
    if (inForEach && (next == TokenKind::Comma || next == TokenKind::CloseBracket))
        return factory.emptyIdentifierName();

    Token identifier;
    if (next == TokenKind::Identifier) {
        identifier = consume();
    }
    else if (next != TokenKind::Dot && next != TokenKind::DoubleColon &&
             (options & NameOptions::ExpectingExpression)) {
        addDiag(diag::ExpectedExpression, peek().location());
        identifier = Token::createMissing(alloc, TokenKind::Identifier, peek().location());
    }
    else {
        identifier = expect(TokenKind::Identifier);
    }

    switch (peek().kind) {
        case TokenKind::Hash: {
            auto parameterValues = parseParameterValueAssignment();
            ASSERT(parameterValues);
            return factory.className(identifier, *parameterValues);
        }
        case TokenKind::OpenBracket: {
            uint32_t index = 1;
            scanTypePart<isSemicolon>(index, TokenKind::OpenBracket, TokenKind::CloseBracket);
            if (!inForEach || peek(index).kind != TokenKind::CloseParenthesis) {
                SmallVectorSized<ElementSelectSyntax*, 4> buffer;
                do {
                    buffer.append(&parseElementSelect());
                } while (peek(TokenKind::OpenBracket));

                return factory.identifierSelectName(identifier, buffer.copy(alloc));
            }
            else {
                return factory.identifierName(identifier);
            }
        }
        default:
            return factory.identifierName(identifier);
    }
}

ParameterValueAssignmentSyntax* Parser::parseParameterValueAssignment() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();
    return &factory.parameterValueAssignment(hash, parseArgumentList());
}

ArgumentListSyntax& Parser::parseArgumentList() {
    Token openParen;
    Token closeParen;
    span<TokenOrSyntax> list;

    parseSeparatedList<isPossibleArgument, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, list,
        closeParen, diag::ExpectedArgument, [this] { return &parseArgument(); });

    return factory.argumentList(openParen, list, closeParen);
}

ArgumentSyntax& Parser::parseArgument() {
    // check for empty arguments
    if (peek(TokenKind::Comma))
        return factory.emptyArgument();

    // check for named arguments
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);

        auto [innerOpenParen, innerCloseParen, expr] =
            parseGroupOrSkip(TokenKind::OpenParenthesis, TokenKind::CloseParenthesis,
                             [this]() { return &parseExpression(); });

        return factory.namedArgument(dot, name, innerOpenParen, expr, innerCloseParen);
    }

    return factory.orderedArgument(parseExpression());
}

PatternSyntax& Parser::parsePattern() {
    switch (peek().kind) {
        case TokenKind::DotStar:
            return factory.wildcardPattern(consume());
        case TokenKind::Dot: {
            auto dot = consume();
            return factory.variablePattern(dot, expect(TokenKind::Identifier));
        }
        case TokenKind::TaggedKeyword: {
            auto tagged = consume();
            auto name = expect(TokenKind::Identifier);
            // TODO: optional trailing pattern
            return factory.taggedPattern(tagged, name, nullptr);
        }
        case TokenKind::ApostropheOpenBrace:
            // TODO: assignment pattern
            break;
        default:
            break;
    }
    // otherwise, it's either an expression or an error (parseExpression will handle that for us)
    return factory.expressionPattern(parseSubExpression(ExpressionOptions::None, 0));
}

ConditionalPredicateSyntax& Parser::parseConditionalPredicate(ExpressionSyntax& first,
                                                              TokenKind endKind, Token& end) {
    SmallVectorSized<TokenOrSyntax, 4> buffer;

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = &factory.matchesClause(matches, parsePattern());
    }

    buffer.append(&factory.conditionalPattern(first, matchesClause));
    if (peek(TokenKind::TripleAnd))
        buffer.append(consume());

    parseSeparatedList<isPossibleExpressionOrTripleAnd, isEndOfConditionalPredicate>(
        buffer, endKind, TokenKind::TripleAnd, end, diag::ExpectedConditionalPattern,
        [this] { return &parseConditionalPattern(); });

    return factory.conditionalPredicate(buffer.copy(alloc));
}

ConditionalPatternSyntax& Parser::parseConditionalPattern() {
    auto& expr = parseSubExpression(ExpressionOptions::None, 0);

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = &factory.matchesClause(matches, parsePattern());
    }

    return factory.conditionalPattern(expr, matchesClause);
}

EventExpressionSyntax& Parser::parseEventExpression() {
    EventExpressionSyntax* left;
    auto kind = peek().kind;
    if (kind == TokenKind::OpenParenthesis) {
        auto openParen = consume();
        auto& expr = parseEventExpression();
        auto closeParen = expect(TokenKind::CloseParenthesis);
        left = &factory.parenthesizedEventExpression(openParen, expr, closeParen);
    }
    else {
        Token edge;
        if (kind == TokenKind::PosEdgeKeyword || kind == TokenKind::NegEdgeKeyword ||
            kind == TokenKind::EdgeKeyword) {
            edge = consume();
        }

        auto& expr = parseSubExpression(
            ExpressionOptions::AllowPatternMatch | ExpressionOptions::EventExpressionContext, 0);
        left = &factory.signalEventExpression(edge, expr);
    }

    kind = peek().kind;
    if (kind == TokenKind::Comma || kind == TokenKind::OrKeyword) {
        auto op = consume();
        left = &factory.binaryEventExpression(*left, op, parseEventExpression());
    }
    return *left;
}

ExpressionSyntax& Parser::parseNewExpression(ExpressionSyntax* scope) {
    if (scope && scope->kind != SyntaxKind::ClassScope) {
        // TODO: verify this error message makes sense
        addDiag(diag::ExpectedClassScope, scope->getFirstToken().location());
        return *scope;
    }
    auto newKeyword = expect(TokenKind::NewKeyword);
    auto kind = peek().kind;

    if (kind == TokenKind::OpenBracket) {
        // new array
        auto openBracket = consume();
        auto& sizeExpr = parseExpression();
        auto closeBracket = expect(TokenKind::CloseBracket);

        ParenthesizedExpressionSyntax* initializer = nullptr;
        if (peek(TokenKind::OpenParenthesis)) {
            auto openParen = consume();
            auto& initializerExpr = parseExpression();
            initializer = &factory.parenthesizedExpression(openParen, initializerExpr,
                                                           expect(TokenKind::CloseParenthesis));
        }
        return factory.newArrayExpression(newKeyword, openBracket, sizeExpr, closeBracket,
                                          initializer);
    }

    // new class
    ArgumentListSyntax* arguments = nullptr;
    if (kind == TokenKind::OpenParenthesis)
        arguments = &parseArgumentList();
    else if (!scope && isPossibleExpression(kind))
        return factory.newExpression(newKeyword, parseExpression());

    return factory.newClassExpression(scope ? &scope->as<ClassScopeSyntax>() : nullptr, newKeyword,
                                      arguments);
}

TimingControlSyntax* Parser::parseTimingControl() {
    switch (peek().kind) {
        case TokenKind::Hash:
        case TokenKind::DoubleHash: {
            auto hash = consume();
            ExpressionSyntax* delay;
            if (hash.kind == TokenKind::DoubleHash && peek(TokenKind::OpenBracket)) {
                if (peek(1).kind == TokenKind::Star || peek(1).kind == TokenKind::Plus) {
                    Token openBracket = consume();
                    Token op = consume();
                    return &factory.shortcutCycleDelayRange(hash, openBracket, op,
                                                            expect(TokenKind::CloseBracket));
                }
                else {
                    delay = &parseElementSelect();
                }
            }
            else {
                delay = &parsePrimaryExpression();
            }

            SyntaxKind kind =
                hash.kind == TokenKind::Hash ? SyntaxKind::DelayControl : SyntaxKind::CycleDelay;
            return &factory.delay(kind, hash, *delay);
        }
        case TokenKind::At: {
            auto at = consume();
            switch (peek().kind) {
                case TokenKind::OpenParenthesis: {
                    auto openParen = consume();
                    if (peek(TokenKind::Star)) {
                        auto star = consume();
                        return &factory.implicitEventControl(at, openParen, star,
                                                             expect(TokenKind::CloseParenthesis));
                    }

                    auto& eventExpr = parseEventExpression();
                    auto closeParen = expect(TokenKind::CloseParenthesis);
                    return &factory.eventControlWithExpression(
                        at, factory.parenthesizedEventExpression(openParen, eventExpr, closeParen));
                }
                case TokenKind::OpenParenthesisStar: {
                    // Special case since @(*) will be lexed as '@' '(*' ')'
                    auto openParen = consume();
                    return &factory.implicitEventControl(at, openParen, Token(),
                                                         expect(TokenKind::CloseParenthesis));
                }
                case TokenKind::Star:
                    return &factory.implicitEventControl(at, Token(), consume(), Token());
                default:
                    return &factory.eventControl(at, parseName());
            }
        }
        case TokenKind::RepeatKeyword: {
            auto repeat = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            return &factory.repeatedEventControl(repeat, openParen, expr, closeParen,
                                                 parseTimingControl());
        }
        default:
            return nullptr;
    }
}

ExpressionSyntax& Parser::parseArrayOrRandomizeWithClause() {
    auto with = consume();
    if (!peek(TokenKind::OpenParenthesis))
        return factory.randomizeMethodWithClause(with, nullptr, parseConstraintBlock());

    auto openParen = consume();
    if (peek(TokenKind::CloseParenthesis)) {
        auto idList = &factory.identifierList(openParen, nullptr, consume());
        return factory.randomizeMethodWithClause(with, idList, parseConstraintBlock());
    }

    if (!peek(TokenKind::Identifier) ||
        (peek(1).kind == TokenKind::CloseParenthesis && peek(2).kind != TokenKind::OpenBrace)) {

        auto& expr = parseExpression();
        return factory.withClause(with, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    // otherwise we have an identifier list here
    Token closeParen;
    SmallVectorSized<TokenOrSyntax, 4> buffer;
    parseSeparatedList<isIdentifierOrComma, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, diag::ExpectedIdentifier,
        [this] { return &factory.identifierName(consume()); });

    auto& idList = factory.identifierList(openParen, buffer.copy(alloc), closeParen);
    return factory.randomizeMethodWithClause(with, &idList, parseConstraintBlock());
}

} // namespace slang
