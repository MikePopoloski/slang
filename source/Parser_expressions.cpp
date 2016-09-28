//------------------------------------------------------------------------------
// Parser_expressions.cpp
// Expression-related parsing methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Parser.h"

#include "Lexer.h"

namespace slang {

ExpressionSyntax* Parser::parseExpression() {
    return parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
}

ExpressionSyntax* Parser::parseMinTypMaxExpression() {
    ExpressionSyntax* first = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto typ = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);
    auto colon2 = expect(TokenKind::Colon);
    auto max = parseSubExpression(ExpressionOptions::AllowPatternMatch, 0);

    return alloc.emplace<MinTypMaxExpressionSyntax>(first, colon1, typ, colon2, max);
}

ExpressionSyntax* Parser::parseSubExpression(ExpressionOptions::Enum options, int precedence) {
    ExpressionSyntax* leftOperand = nullptr;
    int newPrecedence = 0;

    auto current = peek();
    if (current.kind == TokenKind::NewKeyword)
        return parseNewExpression();
    /*else if (isPossibleDelayOrEventControl(current.kind)) {
        auto timingControl = parseTimingControl();
        return alloc.emplace<TimingControlExpressionSyntax>(timingControl, parseExpression());
    }*/
    else if (current.kind == TokenKind::TaggedKeyword) {
        // TODO: check for trailing expression
        auto tagged = consume();
        auto member = expect(TokenKind::Identifier);
        return alloc.emplace<TaggedUnionExpressionSyntax>(tagged, member, nullptr);
    }

    SyntaxKind opKind = getUnaryPrefixExpression(current.kind);
    if (opKind != SyntaxKind::Unknown)
        leftOperand = parsePrefixExpression(options, opKind);
    else
        leftOperand = parsePrimaryExpression();

    while (true) {
        // either a binary operator, or we're done
        current = peek();
        opKind = getBinaryExpression(current.kind);
        if (opKind == SyntaxKind::Unknown)
            break;

        // the "or" operator in event expressions is special, we don't handle it here
        if (opKind == SyntaxKind::OrSequenceExpression && (options & ExpressionOptions::EventExpressionContext))
            break;

        // we have to special case '<=', which can be less than or nonblocking assignment depending on context
        if (opKind == SyntaxKind::LessThanEqualExpression && (options & ExpressionOptions::ProceduralAssignmentContext)) {
            options = (ExpressionOptions::Enum)(options & ~ExpressionOptions::ProceduralAssignmentContext);
            opKind = SyntaxKind::NonblockingAssignmentExpression;
        }

        // see if we should take this operator or if it's part of our parent due to precedence
        newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        if (opKind == SyntaxKind::InsideExpression)
            leftOperand = parseInsideExpression(leftOperand);
        else {
            auto opToken = consume();
            auto attributes = parseAttributes();
            auto rightOperand = parseSubExpression(options, newPrecedence);
            leftOperand = alloc.emplace<BinaryExpressionSyntax>(opKind, leftOperand, opToken, attributes, rightOperand);
        }
    }

    // can't nest pattern matching expressions
    if (options & ExpressionOptions::AllowPatternMatch) {
        // if we see the matches keyword or &&& we're in a pattern conditional predicate
        // if we see a question mark, we were in a simple conditional predicate (at the precedence level one beneath logical-or)
        auto logicalOrPrecedence = getPrecedence(SyntaxKind::LogicalOrExpression);
        if (current.kind == TokenKind::MatchesKeyword || current.kind == TokenKind::TripleAnd ||
            (current.kind == TokenKind::Question && precedence < logicalOrPrecedence)) {

            Token question;
            auto predicate = parseConditionalPredicate(leftOperand, TokenKind::Question, question);
            auto attributes = parseAttributes();
            auto left = parseSubExpression(options, logicalOrPrecedence - 1);
            auto colon = expect(TokenKind::Colon);
            auto right = parseSubExpression(options, logicalOrPrecedence - 1);
            leftOperand = alloc.emplace<ConditionalExpressionSyntax>(predicate, question, attributes, left, colon, right);
        }
    }

    return leftOperand;
}

ExpressionSyntax* Parser::parsePrefixExpression(ExpressionOptions::Enum options, SyntaxKind opKind) {
    switch (opKind) {
        case SyntaxKind::UnarySequenceDelayExpression:
        case SyntaxKind::UnarySequenceEventExpression: {
            auto timing = parseTimingControl();
            return alloc.emplace<TimingControlExpressionSyntax>(timing, parseExpression());
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

    ExpressionSyntax* operand = parseSubExpression(options, getPrecedence(opKind));
    return alloc.emplace<PrefixUnaryExpressionSyntax>(opKind, opToken, attributes, operand);
}

ExpressionSyntax* Parser::parsePrimaryExpression() {
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
            expr = alloc.emplace<LiteralExpressionSyntax>(getLiteralExpression(literal.kind), literal);
            break;
        }
        case TokenKind::RealLiteral: {
            // have to check for overflow here, now that we know this is actually a real
            auto literal = consume();
            ASSERT(literal.numericValue().type == NumericValue::Real);
            if (!std::isfinite(literal.numericValue().real))
                addError(DiagCode::RealExponentOverflow, literal.location());
            expr = alloc.emplace<LiteralExpressionSyntax>(SyntaxKind::RealLiteralExpression, literal);
            break;
        }
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
            expr = parseIntegerExpression();
            break;
        case TokenKind::SystemIdentifier: {
            auto identifier = consume();
            expr = alloc.emplace<KeywordNameSyntax>(SyntaxKind::SystemName, identifier);
            break;
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            expr = parseMinTypMaxExpression();

            auto closeParen = expect(TokenKind::CloseParenthesis);
            expr = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, expr, closeParen);
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
                    expr = alloc.emplace<EmptyQueueExpressionSyntax>(openBrace, consume());
                    break;
                case TokenKind::LeftShift:
                case TokenKind::RightShift:
                    expr = parseStreamConcatenation(openBrace);
                    break;
                default: {
                    auto first = parseExpression();
                    if (!peek(TokenKind::OpenBrace))
                        expr = parseConcatenation(openBrace, first);
                    else {
                        auto openBraceInner = consume();
                        auto concat = parseConcatenation(openBraceInner, nullptr);
                        auto closeBrace = expect(TokenKind::CloseBrace);
                        expr = alloc.emplace<MultipleConcatenationExpressionSyntax>(openBrace, first, concat, closeBrace);
                    }
                    break;
                }
            }
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
            if (isPossibleDataType(kind) && kind != TokenKind::Identifier && kind != TokenKind::UnitSystemName) {
                auto type = parseDataType(/* allowImplicit */ false);
                if (peek(TokenKind::ApostropheOpenBrace))
                    expr = parseAssignmentPatternExpression(type);
                else
                    expr = type;
            }
            else {
                // parseName() will insert a missing identifier token for the error case
                // TODO: better error for "expected expression" instead of "expected identifier"
                auto name = parseName();
                if (peek(TokenKind::ApostropheOpenBrace))
                    expr = parseAssignmentPatternExpression(alloc.emplace<NamedTypeSyntax>(name));
                else {
                    // otherwise just a name expression
                    expr = name;
                }
            }
            break;
    }
    return parsePostfixExpression(expr);
}

ExpressionSyntax* Parser::parseIntegerExpression() {
    Token sizeToken;
    Token baseToken;
    uint32_t sizeBits = 32;

    auto token = consume();
    if (token.kind == TokenKind::IntegerBase)
        baseToken = token;
    else {
        ASSERT(token.numericValue().type == NumericValue::Integer);
        uint64_t tokenValue = token.numericValue().integer;

        if (!peek(TokenKind::IntegerBase)) {
            if (tokenValue > INT32_MAX)
                addError(DiagCode::SignedIntegerOverflow, token.location());
            return alloc.emplace<LiteralExpressionSyntax>(SyntaxKind::IntegerLiteralExpression, token);
        }

        sizeToken = token;
        baseToken = consume();

        // TODO: move this constant somewhere
        static const int MaxLiteralBits = 65535;
        if (tokenValue == 0) {
            sizeBits = 32; // just pick something so we can keep going
            addError(DiagCode::LiteralSizeIsZero, token.location());
        }
        else if (tokenValue > MaxLiteralBits) {
            sizeBits = MaxLiteralBits;
            addError(DiagCode::LiteralSizeTooLarge, token.location()) << MaxLiteralBits;
        }
        else {
            sizeBits = (uint32_t)tokenValue;
        }
    }

    // at this point we expect to see vector digits, but they could be split out into other token types
    // because of hex literals
    auto first = peek();
    if (!isPossibleVectorDigit(first.kind)) {
        addError(DiagCode::ExpectedVectorDigits, first.location());
        return alloc.emplace<IntegerVectorExpressionSyntax>(sizeToken, baseToken, Token::createMissing(alloc, TokenKind::IntegerLiteral, first.location()));
    }

    Token next = first;
    uint32_t length = 0;
    LiteralBase base = baseToken.numericFlags().base;
    bool stillGood = true;

	vectorBuilder.start();
    do {
        length += next.rawText().length();
        consume();
        if (stillGood)
            stillGood = Lexer::checkVectorDigits(getDiagnostics(), vectorBuilder, next, base, false);
        next = peek();
    } while (isPossibleVectorDigit(next.kind) && next.trivia().empty());

    StringRef rawText(first.rawText().begin(), length);
    NumericValue value;
    if (stillGood)
        value = vectorBuilder.finish(base, sizeBits, first.location());

    auto info = alloc.emplace<Token::Info>(first.trivia(), rawText, first.location(), 0);
    info->numInfo.value = value;
    info->numInfo.numericFlags = NumericTokenFlags();

    return alloc.emplace<IntegerVectorExpressionSyntax>(sizeToken, baseToken, Token(TokenKind::IntegerLiteral, info));
}

ExpressionSyntax* Parser::parseInsideExpression(ExpressionSyntax* expr) {
    auto inside = expect(TokenKind::InsideKeyword);
    auto list = parseOpenRangeList();
    return alloc.emplace<InsideExpressionSyntax>(expr, inside, list);
}

OpenRangeListSyntax* Parser::parseOpenRangeList() {
    Token openBrace;
    Token closeBrace;
    ArrayRef<TokenOrSyntax> list;

    parseSeparatedList<isPossibleOpenRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        openBrace,
        list,
        closeBrace,
        DiagCode::ExpectedOpenRangeElement,
        [this](bool) { return parseOpenRangeElement(); }
    );

    return alloc.emplace<OpenRangeListSyntax>(openBrace, list, closeBrace);
}

ExpressionSyntax* Parser::parseOpenRangeElement() {
    if (!peek(TokenKind::OpenBracket))
        return parseExpression();
    return parseElementSelect();
}

ConcatenationExpressionSyntax* Parser::parseConcatenation(Token openBrace, ExpressionSyntax* first) {
    auto buffer = tosPool.get();
    if (first) {
        // it's possible to have just one element in the concatenation list, so check for a close brace
        buffer->append(first);
        if (peek(TokenKind::CloseBrace))
            return alloc.emplace<ConcatenationExpressionSyntax>(openBrace, buffer->copy(alloc), consume());

        buffer->append(expect(TokenKind::Comma));
    }

    Token closeBrace;
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        buffer,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        closeBrace,
        DiagCode::ExpectedExpression,
        [this](bool) { return parseExpression(); }
    );
    return alloc.emplace<ConcatenationExpressionSyntax>(openBrace, buffer->copy(alloc), closeBrace);
}

StreamingConcatenationExpressionSyntax* Parser::parseStreamConcatenation(Token openBrace) {
    auto op = consume();
    ExpressionSyntax* sliceSize = nullptr;
    if (!peek(TokenKind::OpenBrace))
        sliceSize = parseExpression();

    Token openBraceInner;
    Token closeBraceInner;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        TokenKind::OpenBrace,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        openBraceInner,
        list,
        closeBraceInner,
        DiagCode::ExpectedStreamExpression,
        [this](bool) { return parseStreamExpression(); }
    );

    auto closeBrace = expect(TokenKind::CloseBrace);
    return alloc.emplace<StreamingConcatenationExpressionSyntax>(
        openBrace,
        op,
        sliceSize,
        openBraceInner,
        list,
        closeBraceInner,
        closeBrace
        );
}

StreamExpressionSyntax* Parser::parseStreamExpression() {
    auto expr = parseExpression();

    StreamExpressionWithRange* withRange = nullptr;
    if (peek(TokenKind::WithKeyword)) {
        auto with = consume();
        withRange = alloc.emplace<StreamExpressionWithRange>(with, parseElementSelect());
    }

    return alloc.emplace<StreamExpressionSyntax>(expr, withRange);
}

AssignmentPatternExpressionSyntax* Parser::parseAssignmentPatternExpression(DataTypeSyntax* type) {
    auto openBrace = expect(TokenKind::ApostropheOpenBrace);

    // we either have an expression here, or the default keyword for a pattern key
    ExpressionSyntax* firstExpr;
    if (peek(TokenKind::DefaultKeyword))
        firstExpr = alloc.emplace<LiteralExpressionSyntax>(SyntaxKind::DefaultPatternKeyExpression, consume());
    else
        firstExpr = parseExpression();

    Token closeBrace;
    AssignmentPatternSyntax* pattern;
    auto buffer = tosPool.get();

    switch (peek().kind) {
        case TokenKind::Colon:
            buffer->append(parseAssignmentPatternItem(firstExpr));
            parseSeparatedList<isPossibleExpressionOrCommaOrDefault, isEndOfBracedList>(
                buffer,
                TokenKind::CloseBrace,
                TokenKind::Comma,
                closeBrace,
                DiagCode::ExpectedAssignmentKey,
                [this](bool) { return parseAssignmentPatternItem(nullptr); }
            );
            pattern = alloc.emplace<StructuredAssignmentPatternSyntax>(
                openBrace,
                buffer->copy(alloc),
                closeBrace
                );
            break;
        case TokenKind::OpenBrace: {
            auto innerOpenBrace = consume();
            parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer,
                TokenKind::CloseBrace,
                TokenKind::Comma,
                closeBrace,
                DiagCode::ExpectedExpression,
                [this](bool) { return parseExpression(); }
            );
            pattern = alloc.emplace<ReplicatedAssignmentPatternSyntax>(
                openBrace,
                firstExpr,
                innerOpenBrace,
                buffer->copy(alloc),
                closeBrace,
                expect(TokenKind::CloseBrace)
                );
            break;
        }
        default:
            buffer->append(firstExpr);
            parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer,
                TokenKind::CloseBrace,
                TokenKind::Comma,
                closeBrace,
                DiagCode::ExpectedExpression,
                [this](bool) { return parseExpression(); }
            );
            pattern = alloc.emplace<SimpleAssignmentPatternSyntax>(
                openBrace,
                buffer->copy(alloc),
                closeBrace
                );
            break;
    }
    return alloc.emplace<AssignmentPatternExpressionSyntax>(type, pattern);
}

AssignmentPatternItemSyntax* Parser::parseAssignmentPatternItem(ExpressionSyntax* key) {
    if (!key)
        key = parseExpression();

    auto colon = expect(TokenKind::Colon);
    return alloc.emplace<AssignmentPatternItemSyntax>(key, colon, parseExpression());
}

ElementSelectSyntax* Parser::parseElementSelect() {
    auto openBracket = expect(TokenKind::OpenBracket);
    auto selector = parseElementSelector();
    auto closeBracket = expect(TokenKind::CloseBracket);
    return alloc.emplace<ElementSelectSyntax>(openBracket, selector, closeBracket);
}

SelectorSyntax* Parser::parseElementSelector() {
    auto expr = parseExpression();
    switch (peek().kind) {
        case TokenKind::Colon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::SimpleRangeSelect, expr, range, parseExpression());
        }
        case TokenKind::PlusColon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::AscendingRangeSelect, expr, range, parseExpression());
        }
        case TokenKind::MinusColon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::DescendingRangeSelect, expr, range, parseExpression());
        }
        default:
            return alloc.emplace<BitSelectSyntax>(expr);
    }
}

ExpressionSyntax* Parser::parsePostfixExpression(ExpressionSyntax* expr) {
    while (true) {
        switch (peek().kind) {
            case TokenKind::OpenBracket:
                expr = alloc.emplace<ElementSelectExpressionSyntax>(expr, parseElementSelect());
                break;
            case TokenKind::Dot: {
                auto dot = consume();
                auto name = expect(TokenKind::Identifier);
                expr = alloc.emplace<MemberAccessExpressionSyntax>(expr, dot, name);
                break;
            }
            case TokenKind::OpenParenthesis:
                expr = alloc.emplace<InvocationExpressionSyntax>(expr, nullptr, parseArgumentList());
                break;
            case TokenKind::DoublePlus:
            case TokenKind::DoubleMinus: {
                // can't have any other postfix expressions after inc/dec
                auto op = consume();
                return alloc.emplace<PostfixUnaryExpressionSyntax>(getUnaryPostfixExpression(op.kind), expr, nullptr, op);
            }
            case TokenKind::Apostrophe: {
                auto apostrophe = consume();
                auto openParen = expect(TokenKind::OpenParenthesis);
                auto innerExpr = parseExpression();
                auto closeParen = expect(TokenKind::CloseParenthesis);
                auto parenExpr = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, innerExpr, closeParen);
                expr = alloc.emplace<CastExpressionSyntax>(expr, apostrophe, parenExpr);
                break;
            }
            case TokenKind::OpenParenthesisStar: {
                auto attributes = parseAttributes();
                switch (peek().kind) {
                    case TokenKind::DoublePlus:
                    case TokenKind::DoubleMinus: {
                        auto op = consume();
                        return alloc.emplace<PostfixUnaryExpressionSyntax>(getUnaryPostfixExpression(op.kind), expr, attributes, op);
                    }
                    case TokenKind::OpenParenthesis:
                        expr = alloc.emplace<InvocationExpressionSyntax>(expr, attributes, parseArgumentList());
                        break;
                    default:
                        // otherwise, this has to be a function call without any arguments
                        expr = alloc.emplace<InvocationExpressionSyntax>(expr, attributes, nullptr);
                        break;
                }
                break;
            }
            case TokenKind::WithKeyword:
                // If we see bracket right after the with keyword, this is actually part of a stream expression
                // return and let the call further up the stack handle it.
                if (peek(1).kind == TokenKind::OpenBracket)
                    return expr;
                expr = parseArrayOrRandomizeWithClause();
                break;
            default:
                return expr;
        }
    }
}

NameSyntax* Parser::parseName() {
    NameSyntax* name = parseNamePart();

    bool usedDot = false;
    bool reportedError = false;

    auto kind = peek().kind;
    while (kind == TokenKind::Dot || kind == TokenKind::DoubleColon) {
        auto separator = consume();
        if (kind == TokenKind::Dot)
            usedDot = true;
        else if (usedDot && !reportedError) {
            reportedError = true;
            addError(DiagCode::ColonShouldBeDot, separator.location());
        }

        name = alloc.emplace<ScopedNameSyntax>(name, separator, parseNamePart());
        kind = peek().kind;
    }

    return name;
}

NameSyntax* Parser::parseNamePart() {
    auto kind = getKeywordNameExpression(peek().kind);
    if (kind != SyntaxKind::Unknown)
        return alloc.emplace<KeywordNameSyntax>(kind, consume());

    auto identifier = expect(TokenKind::Identifier);
    switch (peek().kind) {
        case TokenKind::Hash: {
            auto parameterValues = parseParameterValueAssignment();
            return alloc.emplace<ClassNameSyntax>(identifier, parameterValues);
        }
        case TokenKind::OpenBracket: {
            auto buffer = nodePool.getAs<ElementSelectSyntax*>();
            do {
                buffer->append(parseElementSelect());
            } while (peek(TokenKind::OpenBracket));

            return alloc.emplace<IdentifierSelectNameSyntax>(identifier, buffer->copy(alloc));
        }
        default:
            return alloc.emplace<IdentifierNameSyntax>(identifier);
    }
}

ParameterValueAssignmentSyntax* Parser::parseParameterValueAssignment() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();
    return alloc.emplace<ParameterValueAssignmentSyntax>(hash, parseArgumentList());
}

ArgumentListSyntax* Parser::parseArgumentList() {
    Token openParen;
    Token closeParen;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseSeparatedList<isPossibleArgument, isEndOfParenList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        openParen,
        list,
        closeParen,
        DiagCode::ExpectedArgument,
        [this](bool) { return parseArgument(); }
    );

    return alloc.emplace<ArgumentListSyntax>(openParen, list, closeParen);
}

ArgumentSyntax* Parser::parseArgument() {
    // check for named arguments
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto innerOpenParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr = nullptr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = parseExpression();

        return alloc.emplace<NamedArgumentSyntax>(dot, name, innerOpenParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return alloc.emplace<OrderedArgumentSyntax>(parseExpression());
}

PatternSyntax* Parser::parsePattern() {
    switch (peek().kind) {
        case TokenKind::DotStar:
            return alloc.emplace<WildcardPatternSyntax>(consume());
        case TokenKind::Dot: {
            auto dot = consume();
            return alloc.emplace<VariablePatternSyntax>(dot, expect(TokenKind::Identifier));
        }
        case TokenKind::TaggedKeyword: {
            auto tagged = consume();
            auto name = expect(TokenKind::Identifier);
            // TODO: optional trailing pattern
            return alloc.emplace<TaggedPatternSyntax>(tagged, name, nullptr);
        }
        case TokenKind::ApostropheOpenBrace:
            // TODO: assignment pattern
            break;
        default:
            break;
    }
    // otherwise, it's either an expression or an error (parseExpression will handle that for us)
    return alloc.emplace<ExpressionPatternSyntax>(parseSubExpression(ExpressionOptions::None, 0));
}

ConditionalPredicateSyntax* Parser::parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token& end) {
    auto buffer = tosPool.get();

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
    }

    buffer->append(alloc.emplace<ConditionalPatternSyntax>(first, matchesClause));
    if (peek(TokenKind::TripleAnd))
        buffer->append(consume());

    parseSeparatedList<isPossibleExpressionOrTripleAnd, isEndOfConditionalPredicate>(
        buffer,
        endKind,
        TokenKind::TripleAnd,
        end,
        DiagCode::ExpectedConditionalPattern,
        [this](bool) { return parseConditionalPattern(); }
    );

    return alloc.emplace<ConditionalPredicateSyntax>(buffer->copy(alloc));
}

ConditionalPatternSyntax* Parser::parseConditionalPattern() {
    auto expr = parseSubExpression(ExpressionOptions::None, 0);

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
    }

    return alloc.emplace<ConditionalPatternSyntax>(expr, matchesClause);
}

EventExpressionSyntax* Parser::parseEventExpression() {
    EventExpressionSyntax* left;
    auto kind = peek().kind;
    if (kind == TokenKind::OpenParenthesis) {
        auto openParen = consume();
        auto expr = parseEventExpression();
        auto closeParen = expect(TokenKind::CloseParenthesis);
        left = alloc.emplace<ParenthesizedEventExpressionSyntax>(openParen, expr, closeParen);
    }
    else {
        Token edge;
        if (kind == TokenKind::PosEdgeKeyword || kind == TokenKind::NegEdgeKeyword || kind == TokenKind::EdgeKeyword)
            edge = consume();

        auto expr = parseSubExpression((ExpressionOptions::Enum)(ExpressionOptions::AllowPatternMatch | ExpressionOptions::EventExpressionContext), 0);
        left = alloc.emplace<SignalEventExpressionSyntax>(edge, expr);
    }

    kind = peek().kind;
    if (kind == TokenKind::Comma || kind == TokenKind::OrKeyword) {
        auto op = consume();
        left = alloc.emplace<BinaryEventExpressionSyntax>(left, op, parseEventExpression());
    }
    return left;
}

ExpressionSyntax* Parser::parseNewExpression() {
    auto newKeyword = consume();
    auto kind = peek().kind;

    if (kind == TokenKind::OpenBracket) {
        // new array
        auto openBracket = consume();
        auto sizeExpr = parseExpression();
        auto closeBracket = expect(TokenKind::CloseBracket);

        ParenthesizedExpressionSyntax* initializer = nullptr;
        if (peek(TokenKind::OpenParenthesis)) {
            auto openParen = consume();
            auto initializerExpr = parseExpression();
            initializer = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, initializerExpr, expect(TokenKind::CloseParenthesis));
        }
        return alloc.emplace<NewArrayExpressionSyntax>(newKeyword, openBracket, sizeExpr, closeBracket, initializer);
    }

    // new class
    ArgumentListSyntax* arguments = nullptr;
    if (kind == TokenKind::OpenParenthesis)
        arguments = parseArgumentList();

    // TODO: handle class scoped new
    return alloc.emplace<NewClassExpressionSyntax>(nullptr, newKeyword, arguments);
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
                    return alloc.emplace<ShortcutCycleDelayRangeSyntax>(hash, openBracket, op, expect(TokenKind::CloseBracket));
                }
                else {
                    delay = parseElementSelect();
                }
            }
            else {
                // TODO: make sure primary expression ends up being the right type
                delay = parsePrimaryExpression();
            }

            SyntaxKind kind = hash.kind == TokenKind::Hash ? SyntaxKind::DelayControl : SyntaxKind::CycleDelay;
            return alloc.emplace<DelaySyntax>(kind, hash, delay);
        }
        case TokenKind::At: {
            auto at = consume();
            if (peek(TokenKind::OpenParenthesis)) {
                auto openParen = consume();
                auto eventExpr = parseEventExpression();
                auto closeParen = expect(TokenKind::CloseParenthesis);
                return alloc.emplace<EventControlWithExpressionSyntax>(at, alloc.emplace<ParenthesizedEventExpressionSyntax>(openParen, eventExpr, closeParen));
            }
            else if (peek(TokenKind::OpenParenthesisStarCloseParenthesis))
                return alloc.emplace<ParenImplicitEventControlSyntax>(at, consume());
            else
                return alloc.emplace<EventControlSyntax>(at, parseName());
        }
        case TokenKind::AtStar:
            return alloc.emplace<ImplicitEventControlSyntax>(consume());
        case TokenKind::RepeatKeyword: {
            auto repeat = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto expr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            return alloc.emplace<RepeatedEventControlSyntax>(repeat, openParen, expr, closeParen, parseTimingControl());
        }
        default:
            return nullptr;
    }
}

ExpressionSyntax* Parser::parseArrayOrRandomizeWithClause() {
    auto with = consume();
    if (!peek(TokenKind::OpenParenthesis))
        return alloc.emplace<RandomizeMethodWithClauseSyntax>(with, nullptr, parseConstraintBlock());

    auto openParen = consume();
    if (peek(TokenKind::CloseParenthesis)) {
        auto idList = alloc.emplace<IdentifierListSyntax>(openParen, nullptr, consume());
        return alloc.emplace<RandomizeMethodWithClauseSyntax>(with, idList, parseConstraintBlock());
    }

    if (!peek(TokenKind::Identifier) || (peek(1).kind == TokenKind::CloseParenthesis && peek(2).kind != TokenKind::OpenBrace)) {
        auto expr = parseExpression();
        return alloc.emplace<ArrayMethodWithClauseSyntax>(with, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    // otherwise we have an identifier list here
    Token closeParen;
    auto buffer = tosPool.get();
    parseSeparatedList<isIdentifierOrComma, isEndOfParenList>(
        buffer,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        closeParen,
        DiagCode::ExpectedIdentifier,
        [this](bool) { return alloc.emplace<IdentifierNameSyntax>(consume()); }
    );

    auto idList = alloc.emplace<IdentifierListSyntax>(openParen, buffer->copy(alloc), closeParen);
    return alloc.emplace<RandomizeMethodWithClauseSyntax>(with, idList, parseConstraintBlock());
}

}