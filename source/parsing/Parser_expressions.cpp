//------------------------------------------------------------------------------
// Parser_expressions.cpp
// Expression-related parsing methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

namespace slang::parsing {

using namespace syntax;

ExpressionSyntax& Parser::parseExpression() {
    return parseSubExpression(ExpressionOptions::None, 0);
}

ExpressionSyntax& Parser::parseMinTypMaxExpression(bitmask<ExpressionOptions> options) {
    ExpressionSyntax& first = parseSubExpression(options, 0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto& typ = parseExpression();
    auto colon2 = expect(TokenKind::Colon);
    auto& max = parseExpression();

    return factory.minTypMaxExpression(first, colon1, typ, colon2, max);
}

ExpressionSyntax& Parser::parseExpressionOrDist(bitmask<ExpressionOptions> options) {
    return parseSubExpression(options | ExpressionOptions::AllowDist, 0);
}

static bool isNewExpr(const ExpressionSyntax* expr) {
    while (true) {
        if (expr->kind == SyntaxKind::ConstructorName)
            return true;

        if (expr->kind != SyntaxKind::ScopedName)
            return false;

        expr = expr->as<ScopedNameSyntax>().right;
    }
}

ExpressionSyntax& Parser::parseSubExpression(bitmask<ExpressionOptions> options, int precedence) {
    auto dg = setDepthGuard();

    auto current = peek();
    if (isPossibleDelayOrEventControl(current.kind)) {
        auto timingControl = parseTimingControl();
        SLANG_ASSERT(timingControl);

        auto& expr = factory.timingControlExpression(*timingControl, parseExpression());
        return parsePostfixExpression(expr, options);
    }
    else if (current.kind == TokenKind::TaggedKeyword) {
        auto tagged = consume();
        auto member = expect(TokenKind::Identifier);

        ExpressionSyntax* expr = nullptr;
        if (isPossibleExpression(peek().kind)) {
            // This is not allowed to be a binary expression,
            // so use a high precedence to avoid taking any
            // binary operators that may trail our tag expr.
            expr = &parseSubExpression(ExpressionOptions::None, INT_MAX);
        }

        return factory.taggedUnionExpression(tagged, member, expr);
    }

    ExpressionSyntax* leftOperand;
    SyntaxKind opKind = getUnaryPrefixExpression(current.kind);
    if (opKind != SyntaxKind::Unknown) {
        auto opToken = consume();
        auto attributes = parseAttributes();
        if (options.has(ExpressionOptions::DisallowAttrs))
            errorIfAttributes(attributes);

        auto& operand = parsePrimaryExpression(options);
        auto& postfix = parsePostfixExpression(operand, options);
        leftOperand = &factory.prefixUnaryExpression(opKind, opToken, attributes, postfix);
    }
    else {
        leftOperand = &parsePrimaryExpression(options);

        // If the primary is a new or scoped new operator we should handle
        // that separately (it doesn't participate in postfix expression parsing).
        if (isNewExpr(leftOperand))
            return parseNewExpression(leftOperand->as<NameSyntax>(), options);

        // Don't try to parse postfix if we didn't find a valid primary to begin with.
        if (leftOperand->kind != SyntaxKind::IdentifierName ||
            !leftOperand->as<IdentifierNameSyntax>().identifier.isMissing()) {
            leftOperand = &parsePostfixExpression(*leftOperand, options);
        }
    }

    options &= ~ExpressionOptions::AllowSuperNewCall;
    return parseBinaryExpression(leftOperand, options, precedence);
}

ExpressionSyntax& Parser::parseBinaryExpression(ExpressionSyntax* left,
                                                bitmask<ExpressionOptions> options,
                                                int precedence) {
    Token current;
    while (true) {
        // either a binary operator, or we're done
        current = peek();
        auto opKind = getBinaryExpression(current.kind);
        if (opKind == SyntaxKind::Unknown) {
            break;
        }
        else if (opKind == SyntaxKind::LogicalImplicationExpression &&
                 options.has(ExpressionOptions::ConstraintContext)) {
            // the implication operator in constraint blocks is special, we don't handle it here
            break;
        }
        else if ((opKind == SyntaxKind::LogicalAndExpression ||
                  opKind == SyntaxKind::LogicalOrExpression) &&
                 options.has(ExpressionOptions::BinsSelectContext)) {
            // The && and || operators in a bins select expression are part of the bins select
            // and not part of this nested sub expression.
            break;
        }
        else if (opKind == SyntaxKind::MultiplyExpression &&
                 peek(1).kind == TokenKind::CloseParenthesis && peek(1).trivia().empty()) {
            // This is an end-of-attribute token, not a multiply.
            break;
        }
        else if (opKind == SyntaxKind::LessThanEqualExpression &&
                 options.has(ExpressionOptions::ProceduralAssignmentContext)) {
            // we have to special case '<=', which can be less than or nonblocking assignment
            // depending
            // on context
            opKind = SyntaxKind::NonblockingAssignmentExpression;
        }

        options &= ~ExpressionOptions::ProceduralAssignmentContext;

        // see if we should take this operator or if it's part of our parent due to precedence
        int newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        if (opKind == SyntaxKind::InsideExpression) {
            left = &parseInsideExpression(*left);
        }
        else if (opKind == SyntaxKind::ExpressionOrDist) {
            auto& dist = parseDistConstraintList();
            left = &factory.expressionOrDist(*left, dist);

            if (!options.has(ExpressionOptions::AllowDist)) {
                addDiag(diag::InvalidDistExpression, dist.dist.location()) << dist.sourceRange();
            }
        }
        else {
            auto opToken = consume();
            auto attributes = parseAttributes();
            auto& rightOperand = parseSubExpression(options, newPrecedence);
            left = &factory.binaryExpression(opKind, *left, opToken, attributes, rightOperand);

            if (isAssignmentOperator(opKind) || options.has(ExpressionOptions::DisallowAttrs))
                errorIfAttributes(attributes);
        }
    }

    // Handle conditional expressions (and their optional pattern matched predicate).
    // Only do this if we're not already within a conditional pattern context, and if
    // we're at the right precedence level (one lower than a logical-or) to take it.
    int logicalOrPrecedence = getPrecedence(SyntaxKind::LogicalOrExpression);
    if (!options.has(ExpressionOptions::PatternContext) && precedence < logicalOrPrecedence) {
        // If this is the start of a pattern predicate, check whether there's actually a
        // question mark coming up. Otherwise we might be a predicate inside a
        // statement which doesn't need the question.
        bool takeConditional = current.kind == TokenKind::Question;
        if (current.kind == TokenKind::MatchesKeyword || current.kind == TokenKind::TripleAnd)
            takeConditional = isConditionalExpression();

        if (takeConditional) {
            Token question;
            auto& predicate = parseConditionalPredicate(*left, TokenKind::Question, question);
            auto attributes = parseAttributes();
            if (options.has(ExpressionOptions::DisallowAttrs))
                errorIfAttributes(attributes);

            auto& lhs = parseSubExpression(options, logicalOrPrecedence - 1);
            auto colon = expect(TokenKind::Colon);
            auto& rhs = parseSubExpression(options, logicalOrPrecedence - 1);
            left = &factory.conditionalExpression(predicate, question, attributes, lhs, colon, rhs);
        }
    }

    return *left;
}

ExpressionSyntax& Parser::parsePrimaryExpression(bitmask<ExpressionOptions> options) {
    TokenKind kind = peek().kind;
    switch (kind) {
        case TokenKind::StringLiteral:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::NullKeyword:
        case TokenKind::Dollar: {
            auto literal = consume();
            return factory.literalExpression(getLiteralExpression(literal.kind), literal);
        }
        case TokenKind::TimeLiteral:
            return factory.literalExpression(SyntaxKind::TimeLiteralExpression,
                                             numberParser.parseReal(*this));
        case TokenKind::RealLiteral:
            return factory.literalExpression(SyntaxKind::RealLiteralExpression,
                                             numberParser.parseReal(*this));
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
            return parseIntegerExpression(options.has(ExpressionOptions::DisallowVectors));
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto expr = &parseMinTypMaxExpression(options & ExpressionOptions::AllowDist);
            auto closeParen = expect(TokenKind::CloseParenthesis);

            if (expr->kind == SyntaxKind::ExpressionOrDist &&
                options.has(ExpressionOptions::AllowDist)) {
                addDiag(diag::NonstandardDist, openParen.location()) << closeParen.range();
            }

            return factory.parenthesizedExpression(openParen, *expr, closeParen);
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
                    return factory.emptyQueueExpression(openBrace, consume());
                case TokenKind::LeftShift:
                case TokenKind::RightShift:
                    return parseStreamConcatenation(openBrace);
                default: {
                    auto& first = parseExpression();
                    if (!peek(TokenKind::OpenBrace))
                        return parseConcatenation(openBrace, &first);
                    else {
                        auto openBraceInner = consume();
                        auto& concat = parseConcatenation(openBraceInner, nullptr);
                        auto closeBrace = expect(TokenKind::CloseBrace);
                        return factory.multipleConcatenationExpression(openBrace, first, concat,
                                                                       closeBrace);
                    }
                }
            }
        }
        case TokenKind::SignedKeyword:
        case TokenKind::UnsignedKeyword:
        case TokenKind::ConstKeyword: {
            auto signing = consume();
            auto apostrophe = expect(TokenKind::Apostrophe);
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& innerExpr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& parenExpr = factory.parenthesizedExpression(openParen, innerExpr, closeParen);
            return factory.signedCastExpression(signing, apostrophe, parenExpr);
        }
        case TokenKind::SystemIdentifier:
            return factory.systemName(consume());
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

                auto& type = parseDataType();
                if (peek(TokenKind::ApostropheOpenBrace))
                    return parseAssignmentPatternExpression(&type);
                else
                    return type;
            }
            else {
                bitmask<NameOptions> nameOptions = NameOptions::ExpectingExpression;
                if (options.has(ExpressionOptions::SequenceExpr))
                    nameOptions |= NameOptions::SequenceExpr;

                // parseName() will insert a missing identifier token for the error case
                auto& name = parseName(nameOptions);
                if (peek(TokenKind::ApostropheOpenBrace))
                    return parseAssignmentPatternExpression(&factory.namedType(name));
                else {
                    // otherwise just a name expression
                    return name;
                }
            }
    }
}

ExpressionSyntax& Parser::parseIntegerExpression(bool disallowVector) {
    auto result = disallowVector ? numberParser.parseSimpleInt(*this)
                                 : numberParser.parseInteger(*this);

    if (result.isSimple)
        return factory.literalExpression(SyntaxKind::IntegerLiteralExpression, result.value);

    return factory.integerVectorExpression(result.size, result.base, result.value);
}

void Parser::handleExponentSplit(Token token, size_t offset) {
    SmallVector<Token, 4> split;
    Lexer::splitTokens(alloc, getDiagnostics(), getPP().getSourceManager(), token, offset,
                       getPP().getCurrentKeywordVersion(), split);

    pushTokens(split);
}

ExpressionSyntax& Parser::parseInsideExpression(ExpressionSyntax& expr) {
    auto inside = expect(TokenKind::InsideKeyword);
    auto& list = parseRangeList();
    return factory.insideExpression(expr, inside, list);
}

RangeListSyntax& Parser::parseRangeList() {
    Token openBrace;
    Token closeBrace;
    std::span<TokenOrSyntax> list;

    parseList<isPossibleValueRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBrace, list, closeBrace,
        RequireItems::True, diag::ExpectedValueRangeElement,
        [this] { return &parseValueRangeElement(); });

    return factory.rangeList(openBrace, list, closeBrace);
}

ExpressionSyntax& Parser::parseValueRangeElement(bitmask<ExpressionOptions> options) {
    if (!peek(TokenKind::OpenBracket))
        return parseSubExpression(options, 0);

    auto openBracket = consume();
    auto& left = parseExpression();

    Token op;
    if (peek(TokenKind::PlusDivMinus) || peek(TokenKind::PlusModMinus)) {
        op = consume();
        if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, op.range())
                << toString(parseOptions.languageVersion);
        }
    }
    else {
        op = expect(TokenKind::Colon);
    }

    auto& right = parseExpression();
    auto closeBracket = expect(TokenKind::CloseBracket);
    return factory.valueRangeExpression(openBracket, left, op, right, closeBracket);
}

ConcatenationExpressionSyntax& Parser::parseConcatenation(Token openBrace,
                                                          ExpressionSyntax* first) {
    SmallVector<TokenOrSyntax, 8> buffer;
    if (first) {
        // it's possible to have just one element in the concatenation list, so check for a close
        // brace
        buffer.push_back(first);
        if (peek(TokenKind::CloseBrace))
            return factory.concatenationExpression(openBrace, buffer.copy(alloc), consume());

        buffer.push_back(expect(TokenKind::Comma));
    }

    Token closeBrace;
    parseList<isPossibleExpressionOrComma, isEndOfBracedList>(
        buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::False,
        diag::ExpectedExpression, [this] { return &parseExpression(); });
    return factory.concatenationExpression(openBrace, buffer.copy(alloc), closeBrace);
}

StreamingConcatenationExpressionSyntax& Parser::parseStreamConcatenation(Token openBrace) {
    auto op = consume();
    ExpressionSyntax* sliceSize = nullptr;
    if (!peek(TokenKind::OpenBrace))
        sliceSize = &parseExpression();

    Token openBraceInner;
    Token closeBraceInner;
    std::span<TokenOrSyntax> list;

    parseList<isPossibleExpressionOrComma, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBraceInner, list,
        closeBraceInner, RequireItems::True, diag::ExpectedStreamExpression,
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
    if (peek(TokenKind::DefaultKeyword)) {
        firstExpr = &factory.literalExpression(SyntaxKind::DefaultPatternKeyExpression, consume());
    }
    else if (peek(TokenKind::CloseBrace)) {
        // This is an empty pattern -- we'll just warn and continue on.
        addDiag(diag::EmptyAssignmentPattern, openBrace.location());

        auto pattern = &factory.simpleAssignmentPattern(openBrace, std::span<TokenOrSyntax>{},
                                                        consume());
        return factory.assignmentPatternExpression(type, *pattern);
    }
    else {
        firstExpr = &parseExpression();
    }

    Token closeBrace;
    AssignmentPatternSyntax* pattern;
    SmallVector<TokenOrSyntax, 8> buffer;

    switch (peek().kind) {
        case TokenKind::Colon:
            buffer.push_back(&parseAssignmentPatternItem(firstExpr));
            if (peek(TokenKind::Comma)) {
                buffer.push_back(consume());

                parseList<isPossibleExpressionOrCommaOrDefault, isEndOfBracedList>(
                    buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace,
                    RequireItems::False, diag::ExpectedAssignmentKey,
                    [this] { return &parseAssignmentPatternItem(nullptr); });
            }
            else {
                closeBrace = expect(TokenKind::CloseBrace);
            }

            pattern = &factory.structuredAssignmentPattern(openBrace, buffer.copy(alloc),
                                                           closeBrace);
            break;
        case TokenKind::OpenBrace: {
            auto innerOpenBrace = consume();

            parseList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.replicatedAssignmentPattern(openBrace, *firstExpr, innerOpenBrace,
                                                           buffer.copy(alloc), closeBrace,
                                                           expect(TokenKind::CloseBrace));
            break;
        }
        case TokenKind::Comma:
            buffer.push_back(firstExpr);
            buffer.push_back(consume());

            parseList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.simpleAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
        case TokenKind::CloseBrace:
            buffer.push_back(firstExpr);
            closeBrace = consume();
            pattern = &factory.simpleAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
        default:
            // This is an error case; let the list handling code get us out of it.
            buffer.push_back(firstExpr);
            buffer.push_back(expect(TokenKind::Comma));

            parseList<isPossibleExpressionOrComma, isEndOfBracedList>(
                buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::False,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            pattern = &factory.simpleAssignmentPattern(openBrace, buffer.copy(alloc), closeBrace);
            break;
    }
    SLANG_ASSERT(pattern);
    return factory.assignmentPatternExpression(type, *pattern);
}

AssignmentPatternItemSyntax& Parser::parseAssignmentPatternItem(ExpressionSyntax* key) {
    if (!key) {
        if (peek(TokenKind::DefaultKeyword))
            key = &factory.literalExpression(SyntaxKind::DefaultPatternKeyExpression, consume());
        else
            key = &parseExpression();
    }

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

bool Parser::isSequenceRepetition() {
    switch (peek(1).kind) {
        case TokenKind::Star:
        case TokenKind::Equals:
        case TokenKind::MinusArrow:
            return true;
        case TokenKind::Plus:
            return peek(2).kind == TokenKind::CloseBracket;
        default:
            return false;
    }
}

ExpressionSyntax& Parser::parsePostfixExpression(ExpressionSyntax& lhs,
                                                 bitmask<ExpressionOptions> options) {
    ExpressionSyntax* expr = &lhs;

    auto isLiteral = [&] {
        switch (expr->kind) {
            case SyntaxKind::NullLiteralExpression:
            case SyntaxKind::WildcardLiteralExpression:
            case SyntaxKind::StringLiteralExpression:
            case SyntaxKind::RealLiteralExpression:
            case SyntaxKind::TimeLiteralExpression:
            case SyntaxKind::IntegerLiteralExpression:
            case SyntaxKind::UnbasedUnsizedLiteralExpression:
            case SyntaxKind::IntegerVectorExpression:
                return true;
            default:
                return false;
        }
    };

    auto isSelectAllowed = [&] {
        switch (expr->kind) {
            case SyntaxKind::ConcatenationExpression:
            case SyntaxKind::MultipleConcatenationExpression:
            case SyntaxKind::MemberAccessExpression:
            case SyntaxKind::InvocationExpression:
            case SyntaxKind::ArrayOrRandomizeMethodExpression:
            case SyntaxKind::ElementSelectExpression:
                return true;
            default:
                return NameSyntax::isKind(expr->kind);
        }
    };

    while (true) {
        switch (peek().kind) {
            case TokenKind::OpenBracket: {
                if (isLiteral() ||
                    (options.has(ExpressionOptions::SequenceExpr) && isSequenceRepetition())) {
                    return *expr;
                }

                const bool isValid = isSelectAllowed();
                expr = &factory.elementSelectExpression(*expr, parseElementSelect());
                if (!isValid)
                    addDiag(diag::InvalidSelectExpression, expr->sourceRange());

                break;
            }
            case TokenKind::Dot: {
                auto dot = consume();

                Token name;
                switch (peek().kind) {
                    case TokenKind::UniqueKeyword:
                    case TokenKind::AndKeyword:
                    case TokenKind::OrKeyword:
                    case TokenKind::XorKeyword:
                        name = consume();
                        break;
                    default:
                        name = expect(TokenKind::Identifier);
                        break;
                }

                expr = &factory.memberAccessExpression(*expr, dot, name);
                break;
            }
            case TokenKind::OpenParenthesis: {
                if (isStartOfAttrs(0)) {
                    auto attributes = parseAttributes();
                    if (options.has(ExpressionOptions::DisallowAttrs))
                        errorIfAttributes(attributes);

                    switch (peek().kind) {
                        case TokenKind::DoublePlus:
                        case TokenKind::DoubleMinus: {
                            auto op = consume();
                            return factory.postfixUnaryExpression(
                                getUnaryPostfixExpression(op.kind), *expr, attributes, op);
                        }
                        case TokenKind::OpenParenthesis:
                            expr = &factory.invocationExpression(*expr, attributes,
                                                                 &parseArgumentList());
                            break;
                        default:
                            // otherwise, this has to be a function call without any arguments
                            expr = &factory.invocationExpression(*expr, attributes, nullptr);
                            break;
                    }
                }
                else {
                    if (isLiteral())
                        return *expr;

                    auto& args = parseArgumentList();
                    expr = &factory.invocationExpression(*expr, nullptr, &args);
                }
                break;
            }
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
            case TokenKind::WithKeyword:
                // If we see bracket right after the with keyword, this is actually part of a stream
                // expression -- return and let the call further up the stack handle it.
                if (peek(1).kind == TokenKind::OpenBracket)
                    return *expr;

                if (options.has(ExpressionOptions::BinsSelectContext))
                    return *expr;

                expr = &parseArrayOrRandomizeMethod(*expr);
                break;

                // NOTE: If you add a case here, check whether it needs to be added to
                // isBinaryOrPostfixExpression as well.
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

        if (kind == TokenKind::DoubleColon && name->kind == SyntaxKind::IdentifierName)
            meta.classPackageNames.push_back(&name->as<IdentifierNameSyntax>());

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
            case SyntaxKind::ConstructorName:
                addDiag(diag::NewKeywordQualified, separator.location());
                break;
            default:
                break;
        }

        bitmask<NameOptions> nextOptions = options;
        if (previousKind == SyntaxKind::ThisHandle)
            nextOptions |= NameOptions::PreviousWasThis;
        else if (previousKind == SyntaxKind::LocalScope)
            nextOptions |= NameOptions::PreviousWasLocal;

        NameSyntax& rhs = parseNamePart(nextOptions);
        previousKind = rhs.kind;

        name = &factory.scopedName(*name, separator, rhs);
        kind = peek().kind;
    }

    // If we saw super or local, make sure the correct token follows it.
    TokenKind expectedKind = TokenKind::Unknown;
    switch (name->kind) {
        case SyntaxKind::LocalScope:
            expectedKind = TokenKind::DoubleColon;
            break;
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
        // This is a keyword name such as "super", "xor", or "new".
        bool isFirst = (options & NameOptions::IsFirst) != 0;
        if (isSpecialMethodName(kind)) {
            // The built-in methods ("xor", "unique", etc) and are not allowed
            // to be the first element in the name.
            if (!isFirst)
                return factory.keywordName(kind, consume());
        }
        else if (kind == SyntaxKind::ConstructorName) {
            // "new" names are always allowed.
            return factory.keywordName(kind, consume());
        }
        else {
            // Otherwise this is "$unit", "$root", "local", "this", "super".
            // These are only allowed to be the first element in a path, except
            // for "super" which can follow "this".
            if (isFirst ||
                (kind == SyntaxKind::SuperHandle && options.has(NameOptions::PreviousWasThis)) ||
                ((kind == SyntaxKind::SuperHandle || kind == SyntaxKind::ThisHandle) &&
                 options.has(NameOptions::PreviousWasLocal))) {
                return factory.keywordName(kind, consume());
            }
        }

        // Otherwise fall through to the handling below to get an error emitted.
    }

    TokenKind next = peek().kind;
    Token identifier;
    if (next == TokenKind::Identifier) {
        identifier = consume();
    }
    else if (next != TokenKind::Dot && next != TokenKind::DoubleColon &&
             options.has(NameOptions::ExpectingExpression)) {
        if (!haveDiagAtCurrentLoc())
            addDiag(diag::ExpectedExpression, peek().location());
        identifier = Token::createMissing(alloc, TokenKind::Identifier, peek().location());
    }
    else {
        identifier = expect(TokenKind::Identifier);
    }

    switch (peek().kind) {
        case TokenKind::Hash: {
            if (options.has(NameOptions::NoClassScope))
                return factory.identifierName(identifier);

            auto parameterValues = parseParameterValueAssignment();
            SLANG_ASSERT(parameterValues);
            return factory.className(identifier, *parameterValues);
        }
        case TokenKind::OpenBracket: {
            if (options.has(NameOptions::ForeachName)) {
                // For a foreach loop declaration, the final selector
                // brackets need to be parsed specially because they declare
                // loop variable names. All the selectors prior can be
                // parsed as normal selectors.
                SmallVector<ElementSelectSyntax*> buffer;
                do {
                    uint32_t index = 1;
                    scanTypePart<isSemicolon>(index, TokenKind::OpenBracket,
                                              TokenKind::CloseBracket);
                    if (peek(index).kind != TokenKind::OpenBracket &&
                        peek(index).kind != TokenKind::Dot) {
                        break;
                    }

                    buffer.push_back(&parseElementSelect());
                } while (peek(TokenKind::OpenBracket));

                if (buffer.empty())
                    return factory.identifierName(identifier);

                return factory.identifierSelectName(identifier, buffer.copy(alloc));
            }
            else {
                SmallVector<ElementSelectSyntax*> buffer;
                do {
                    // Inside a sequence expression this could be a repetition directive
                    // instead of a selection.
                    if (options.has(NameOptions::SequenceExpr) && isSequenceRepetition()) {
                        if (buffer.empty())
                            return factory.identifierName(identifier);
                        else
                            return factory.identifierSelectName(identifier, buffer.copy(alloc));
                    }

                    buffer.push_back(&parseElementSelect());
                } while (peek(TokenKind::OpenBracket));

                return factory.identifierSelectName(identifier, buffer.copy(alloc));
            }
        }
        default: {
            return factory.identifierName(identifier);
        }
    }
}

ParameterValueAssignmentSyntax* Parser::parseParameterValueAssignment() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();

    Token openParen;
    Token closeParen;
    std::span<TokenOrSyntax> list;
    parseList<isPossibleParamAssignment, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, list,
        closeParen, RequireItems::False, diag::ExpectedArgument,
        [this] { return &parseParamValue(); });

    return &factory.parameterValueAssignment(hash, openParen, list, closeParen);
}

ParamAssignmentSyntax& Parser::parseParamValue() {
    // check for named arguments
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);

        auto [innerOpenParen, innerCloseParen,
              expr] = parseGroupOrSkip(TokenKind::OpenParenthesis, TokenKind::CloseParenthesis,
                                       [this]() { return &parseMinTypMaxExpression(); });

        return factory.namedParamAssignment(dot, name, innerOpenParen, expr, innerCloseParen);
    }

    return factory.orderedParamAssignment(parseMinTypMaxExpression());
}

ArgumentListSyntax& Parser::parseArgumentList() {
    Token openParen;
    Token closeParen;
    std::span<TokenOrSyntax> list;

    parseList<isPossibleArgument, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, list,
        closeParen, RequireItems::False, diag::ExpectedArgument,
        [this] { return &parseArgument(); }, AllowEmpty::True);

    return factory.argumentList(openParen, list, closeParen);
}

ArgumentSyntax& Parser::parseArgument() {
    // check for empty arguments
    if (peek(TokenKind::Comma) || peek(TokenKind::CloseParenthesis))
        return factory.emptyArgument(placeholderToken());

    // check for named arguments
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);

        auto [innerOpenParen, innerCloseParen,
              expr] = parseGroupOrSkip(TokenKind::OpenParenthesis, TokenKind::CloseParenthesis,
                                       [this]() { return &parsePropertyExpr(0); });

        return factory.namedArgument(dot, name, innerOpenParen, expr, innerCloseParen);
    }

    return factory.orderedArgument(parsePropertyExpr(0));
}

PatternSyntax& Parser::parsePattern() {
    switch (peek().kind) {
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto& pattern = parsePattern();
            return factory.parenthesizedPattern(openParen, pattern,
                                                expect(TokenKind::CloseParenthesis));
        }
        case TokenKind::Dot: {
            auto dot = consume();
            if (peek(TokenKind::Star))
                return factory.wildcardPattern(dot, consume());
            return factory.variablePattern(dot, expect(TokenKind::Identifier));
        }
        case TokenKind::TaggedKeyword: {
            auto tagged = consume();
            auto name = expect(TokenKind::Identifier);

            PatternSyntax* pattern = nullptr;
            if (isPossiblePattern(peek().kind))
                pattern = &parsePattern();

            return factory.taggedPattern(tagged, name, pattern);
        }
        case TokenKind::ApostropheOpenBrace: {
            auto openBrace = consume();
            Token closeBrace;
            SmallVector<TokenOrSyntax, 4> buffer;

            if (peek(TokenKind::Identifier) && peek(1).kind == TokenKind::Colon) {
                parseList<isIdentifierOrComma, isCloseBrace>(
                    buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::True,
                    diag::ExpectedPattern, [this]() { return &parseMemberPattern(); });
            }
            else {
                parseList<isPossiblePatternOrComma, isCloseBrace>(
                    buffer, TokenKind::CloseBrace, TokenKind::Comma, closeBrace, RequireItems::True,
                    diag::ExpectedPattern, [this]() {
                        auto& pattern = parsePattern();
                        return &factory.orderedStructurePatternMember(pattern);
                    });
            }

            return factory.structurePattern(openBrace, buffer.copy(alloc), closeBrace);
        }
        default:
            break;
    }

    // otherwise, it's either an expression or an error (parseExpression will handle that for us)
    return factory.expressionPattern(parseSubExpression(ExpressionOptions::PatternContext, 0));
}

StructurePatternMemberSyntax& Parser::parseMemberPattern() {
    auto name = expect(TokenKind::Identifier);
    auto colon = expect(TokenKind::Colon);
    auto& pattern = parsePattern();
    return factory.namedStructurePatternMember(name, colon, pattern);
}

ConditionalPredicateSyntax& Parser::parseConditionalPredicate(ExpressionSyntax& first,
                                                              TokenKind endKind, Token& end) {
    SmallVector<TokenOrSyntax, 4> buffer;

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = &factory.matchesClause(matches, parsePattern());
    }

    buffer.push_back(&factory.conditionalPattern(first, matchesClause));

    if (peek(TokenKind::TripleAnd)) {
        buffer.push_back(consume());
        parseList<isPossibleExpressionOrTripleAnd, isEndOfConditionalPredicate>(
            buffer, endKind, TokenKind::TripleAnd, end, RequireItems::True,
            diag::ExpectedConditionalPattern, [this] { return &parseConditionalPattern(); });
    }
    else {
        end = expect(endKind);
    }

    return factory.conditionalPredicate(buffer.copy(alloc));
}

ConditionalPatternSyntax& Parser::parseConditionalPattern() {
    auto& expr = parseSubExpression(ExpressionOptions::PatternContext, 0);

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = &factory.matchesClause(matches, parsePattern());
    }

    return factory.conditionalPattern(expr, matchesClause);
}

EventExpressionSyntax& Parser::parseSignalEvent() {
    Token edge = parseEdgeKeyword();
    auto& expr = parseExpression();

    IffEventClauseSyntax* iffClause = nullptr;
    if (peek(TokenKind::IffKeyword)) {
        auto iff = consume();
        auto& iffExpr = parseExpression();
        iffClause = &factory.iffEventClause(iff, iffExpr);
    }

    return factory.signalEventExpression(edge, expr, iffClause);
}

EventExpressionSyntax& Parser::parseEventExpression() {
    EventExpressionSyntax* left = nullptr;
    auto kind = peek().kind;
    if (kind == TokenKind::OpenParenthesis) {
        auto openParen = consume();
        auto& expr = parseEventExpression();
        auto closeParen = expect(TokenKind::CloseParenthesis);

        // If the event expression turns out to be interpretable as a simple expression,
        // treat it as such. This is necessary because the next token coming up might
        // be part of a larger binary expression (the opening paren here is ambiguous).
        if (expr.kind == SyntaxKind::SignalEventExpression) {
            auto& see = expr.as<SignalEventExpressionSyntax>();
            if (!see.edge && !see.iffClause) {
                ExpressionSyntax* newExpr = &factory.parenthesizedExpression(openParen, *see.expr,
                                                                             closeParen);

                newExpr = &parsePostfixExpression(*newExpr, ExpressionOptions::None);
                newExpr = &parseBinaryExpression(newExpr, ExpressionOptions::None, 0);

                left = &factory.signalEventExpression(Token(), *newExpr, nullptr);
            }
        }

        if (!left)
            left = &factory.parenthesizedEventExpression(openParen, expr, closeParen);
    }
    else {
        left = &parseSignalEvent();
    }

    kind = peek().kind;
    if (kind == TokenKind::Comma || kind == TokenKind::OrKeyword) {
        auto op = consume();
        left = &factory.binaryEventExpression(*left, op, parseEventExpression());
    }
    return *left;
}

ExpressionSyntax& Parser::parseNewExpression(NameSyntax& newKeyword,
                                             bitmask<ExpressionOptions> options) {
    // If we see an open bracket, this is a dynamic array new expression.
    auto kind = peek().kind;
    if (kind == TokenKind::OpenBracket) {
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

    // Enforce rules for super.new placement.
    bool isSuperNew = false;
    if (newKeyword.kind == SyntaxKind::ScopedName) {
        auto& scoped = newKeyword.as<ScopedNameSyntax>();
        if (scoped.right->kind == SyntaxKind::ConstructorName &&
            scoped.left->getLastToken().kind == TokenKind::SuperKeyword) {
            isSuperNew = true;
            if (!options.has(ExpressionOptions::AllowSuperNewCall)) {
                addDiag(diag::InvalidSuperNew, scoped.right->getFirstToken().location())
                    << newKeyword.sourceRange();
            }
        }
    }

    // Otherwise this is a new-class or copy-class expression.
    // new-class has an optional argument list, copy-class has a required expression.
    // An open paren here would be ambiguous between an arg list and a parenthesized
    // expression -- we resolve by always taking the arg list.
    if (kind == TokenKind::OpenParenthesis) {
        // 1800-2023 added the construct super.new(default) -- check for that here.
        if (isSuperNew && peek(1).kind == TokenKind::DefaultKeyword) {
            auto openParen = consume();
            auto defaultKeyword = consume();
            auto& result = factory.superNewDefaultedArgsExpression(
                newKeyword, openParen, defaultKeyword, expect(TokenKind::CloseParenthesis));

            if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
                addDiag(diag::WrongLanguageVersion, result.sourceRange())
                    << toString(parseOptions.languageVersion);
            }

            return result;
        }
        return factory.newClassExpression(newKeyword, &parseArgumentList());
    }

    if (isPossibleExpression(kind)) {
        if (newKeyword.kind != SyntaxKind::ConstructorName)
            addDiag(diag::ScopedClassCopy, peek().location()) << newKeyword.sourceRange();
        return factory.copyClassExpression(newKeyword, parseExpression());
    }

    return factory.newClassExpression(newKeyword, nullptr);
}

static bool isValidDelayExpr(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::IntegerLiteralExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::RealLiteralExpression:
        case SyntaxKind::ParenthesizedExpression:
            return true;
        default:
            return NameSyntax::isKind(kind);
    }
}

static bool isValidCycleDelay(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::IntegerLiteralExpression:
        case SyntaxKind::IntegerVectorExpression:
        case SyntaxKind::IdentifierName:
        case SyntaxKind::ParenthesizedExpression:
            return true;
        default:
            return false;
    }
}

TimingControlSyntax* Parser::parseTimingControl() {
    switch (peek().kind) {
        case TokenKind::Hash: {
            auto hash = consume();
            if (peek(TokenKind::OneStep))
                return &factory.oneStepDelay(hash, consume());

            auto& delay = parsePrimaryExpression(ExpressionOptions::DisallowVectors);
            if (!isValidDelayExpr(delay.kind))
                addDiag(diag::InvalidDelayValue, delay.sourceRange());

            return &factory.delay(SyntaxKind::DelayControl, hash, delay);
        }
        case TokenKind::DoubleHash: {
            auto hash = consume();
            auto& delay = parsePrimaryExpression(ExpressionOptions::None);
            if (!isValidCycleDelay(delay.kind))
                addDiag(diag::InvalidDelayValue, delay.sourceRange());

            return &factory.delay(SyntaxKind::CycleDelay, hash, delay);
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
                case TokenKind::Star:
                    return &factory.implicitEventControl(at, Token(), consume(), Token());
                case TokenKind::SystemIdentifier:
                    return &factory.eventControl(at,
                                                 parsePrimaryExpression(ExpressionOptions::None));
                default:
                    return &factory.eventControl(at, parseName(NameOptions::NoClassScope));
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

ExpressionSyntax& Parser::parseArrayOrRandomizeMethod(ExpressionSyntax& expr) {
    auto with = consume();

    ParenExpressionListSyntax* args = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        Token openParen, closeParen;
        std::span<TokenOrSyntax> items;
        parseList<isPossibleExpressionOrComma, isEndOfParenList>(
            TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen,
            items, closeParen, RequireItems::False, diag::ExpectedExpression,
            [this] { return &parseExpression(); });

        args = &factory.parenExpressionList(openParen, items, closeParen);
    }

    ConstraintBlockSyntax* constraints = nullptr;
    if (peek(TokenKind::OpenBrace))
        constraints = &parseConstraintBlock(/* isTopLevel */ true);

    return factory.arrayOrRandomizeMethodExpression(expr, with, args, constraints);
}

bool Parser::isConditionalExpression() {
    uint32_t index = 1;
    while (true) {
        TokenKind kind = peek(index++).kind;
        switch (kind) {
            case TokenKind::Question:
                return true;
            case TokenKind::CloseParenthesis:
                return false;
            case TokenKind::OpenParenthesis:
                if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                               TokenKind::CloseParenthesis)) {
                    return false;
                }
                break;
            case TokenKind::OpenBrace:
                if (!scanTypePart<isNotInType>(index, TokenKind::OpenBrace,
                                               TokenKind::CloseBrace)) {
                    return false;
                }
                break;
            case TokenKind::OpenBracket:
                if (!scanTypePart<isNotInType>(index, TokenKind::OpenBracket,
                                               TokenKind::CloseBracket)) {
                    return false;
                }
                break;
            default:
                if (isNotInType(kind))
                    return false;
                break;
        }
    }
}

SelectorSyntax* Parser::parseSequenceRange() {
    auto result = parseElementSelector();
    if (!result) {
        addDiag(diag::ExpectedExpression, peek().location());
    }
    else if (result->kind == SyntaxKind::AscendingRangeSelect ||
             result->kind == SyntaxKind::DescendingRangeSelect) {
        auto& rs = result->as<RangeSelectSyntax>();
        addDiag(diag::InvalidRepeatRange, rs.range.range());
    }
    return result;
}

SequenceExprSyntax& Parser::parseDelayedSequenceExpr(SequenceExprSyntax* first) {
    SmallVector<DelayedSequenceElementSyntax*> elements;
    do {
        Token op, openBracket, closeBracket;
        SelectorSyntax* selector = nullptr;
        ExpressionSyntax* delayVal = nullptr;

        auto hash = expect(TokenKind::DoubleHash);

        if (peek(TokenKind::OpenBracket)) {
            openBracket = consume();
            if ((peek(TokenKind::Star) || peek(TokenKind::Plus)) &&
                peek(1).kind == TokenKind::CloseBracket) {
                op = consume();
            }
            else {
                selector = parseSequenceRange();
            }
            closeBracket = expect(TokenKind::CloseBracket);
        }
        else {
            delayVal = &parsePrimaryExpression(ExpressionOptions::None);
        }

        auto& expr = parseSequencePrimary();
        elements.push_back(&factory.delayedSequenceElement(hash, delayVal, openBracket, op,
                                                           selector, closeBracket, expr));

    } while (peek(TokenKind::DoubleHash));

    return factory.delayedSequenceExpr(first, elements.copy(alloc));
}

static bool isBinaryOrPostfixExpression(TokenKind kind) {
    // NOTE: This deliberately does not include the open bracket because
    // this function is only called on tokens that occur right after a
    // parenthesized expression ends, in a sequence or property context.
    // In those places, an open bracket means something else.
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::OpenParenthesis:
        case TokenKind::Apostrophe:
        case TokenKind::DistKeyword:
        case TokenKind::Question:
            return true;
        default:
            return SyntaxFacts::getBinaryExpression(kind) != SyntaxKind::Unknown;
    }
}

static bool isBinarySequenceExpression(TokenKind kind) {
    switch (kind) {
        case TokenKind::DoubleHash:
        case TokenKind::OpenBracket:
        case TokenKind::IntersectKeyword:
        case TokenKind::ThroughoutKeyword:
        case TokenKind::WithinKeyword:
            return true;
        default:
            return false;
    }
}

SequenceMatchListSyntax* Parser::parseSequenceMatchList(Token& closeParen) {
    if (!peek(TokenKind::Comma)) {
        closeParen = expect(TokenKind::CloseParenthesis);
        return nullptr;
    }

    Token comma;
    std::span<TokenOrSyntax> list;
    parseList<isPossibleArgument, isEndOfParenList>(TokenKind::Comma, TokenKind::CloseParenthesis,
                                                    TokenKind::Comma, comma, list, closeParen,
                                                    RequireItems::True, diag::ExpectedExpression,
                                                    [this] { return &parsePropertyExpr(0); });

    return &factory.sequenceMatchList(comma, list);
}

SequenceRepetitionSyntax* Parser::parseSequenceRepetition() {
    if (!peek(TokenKind::OpenBracket))
        return nullptr;

    auto openBracket = consume();

    Token op;
    switch (peek().kind) {
        case TokenKind::Plus:
        case TokenKind::Equals:
        case TokenKind::MinusArrow:
            op = consume();
            break;
        default:
            op = expect(TokenKind::Star);
            break;
    }

    auto selector = parseElementSelector();
    if (!selector) {
        if (op.kind == TokenKind::Equals || op.kind == TokenKind::MinusArrow)
            addDiag(diag::ExpectedExpression, peek().location());
    }
    else if (op.kind == TokenKind::Plus) {
        addDiag(diag::InvalidRepeatRange, selector->sourceRange());
    }
    else if (selector->kind == SyntaxKind::AscendingRangeSelect ||
             selector->kind == SyntaxKind::DescendingRangeSelect) {
        addDiag(diag::InvalidRepeatRange, selector->as<RangeSelectSyntax>().range.range());
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return &factory.sequenceRepetition(openBracket, op, selector, closeBracket);
}

SequenceExprSyntax& Parser::parseParenthesizedSeqExpr(Token openParen, SequenceExprSyntax& expr) {
    // There is ambiguity between parenthesized sequence expressions and normal
    // expressions. We resolve by always rewriting back to a normal expression
    // if it is possible to do so.
    if (expr.kind == SyntaxKind::SimpleSequenceExpr && peek(TokenKind::CloseParenthesis) &&
        !expr.as<SimpleSequenceExprSyntax>().repetition) {
        ExpressionSyntax* result = expr.as<SimpleSequenceExprSyntax>().expr;
        result = &factory.parenthesizedExpression(openParen, *result,
                                                  expect(TokenKind::CloseParenthesis));

        // It's possible there is more to the original expression here (postfix or binary)
        // which we need to manually parse now since sequence expression parsing will balk
        // at it later.
        if (isBinaryOrPostfixExpression(peek().kind)) {
            result = &parsePostfixExpression(*result, ExpressionOptions::SequenceExpr);
            result = &parseBinaryExpression(
                result, ExpressionOptions::SequenceExpr | ExpressionOptions::AllowDist, 0);
        }

        auto repetition = parseSequenceRepetition();
        return factory.simpleSequenceExpr(*result, repetition);
    }

    Token closeParen;
    auto matchList = parseSequenceMatchList(closeParen);

    auto repetition = parseSequenceRepetition();
    return factory.parenthesizedSequenceExpr(openParen, expr, matchList, closeParen, repetition);
}

SequenceExprSyntax& Parser::parseSequencePrimary() {
    auto current = peek();
    switch (current.kind) {
        case TokenKind::DoubleHash:
            return parseDelayedSequenceExpr(nullptr);
        case TokenKind::At: {
            auto event = parseTimingControl();
            SLANG_ASSERT(event);
            return factory.clockingSequenceExpr(*event,
                                                parseSequenceExpr(0, /* isInProperty */ false));
        }
        case TokenKind::FirstMatchKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseSequenceExpr(0, /* isInProperty */ false);

            Token closeParen;
            auto matchList = parseSequenceMatchList(closeParen);
            return factory.firstMatchSequenceExpr(keyword, openParen, expr, matchList, closeParen);
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto& expr = parseSequenceExpr(0, /* isInProperty */ false);
            return parseParenthesizedSeqExpr(openParen, expr);
        }
        case TokenKind::EdgeKeyword:
        case TokenKind::NegEdgeKeyword:
        case TokenKind::PosEdgeKeyword:
            return parseSignalEvent();
        default: {
            auto& expr = parseExpressionOrDist(ExpressionOptions::SequenceExpr);
            auto repetition = parseSequenceRepetition();
            return factory.simpleSequenceExpr(expr, repetition);
        }
    }
}

SequenceExprSyntax& Parser::parseSequenceExpr(int precedence, bool isInProperty) {
    auto dg = setDepthGuard();

    auto left = &parseSequencePrimary();
    return parseBinarySequenceExpr(left, precedence, isInProperty);
}

SequenceExprSyntax& Parser::parseBinarySequenceExpr(SequenceExprSyntax* left, int precedence,
                                                    bool isInProperty) {
    if (peek(TokenKind::DoubleHash))
        left = &parseDelayedSequenceExpr(left);

    while (true) {
        // either a binary operator, or we're done
        auto opKind = getBinarySequenceExpr(peek().kind);
        if (opKind == SyntaxKind::Unknown)
            break;

        // Inside a property, we don't consume an "and" or "or" expression because
        // we want the parent property parser to get a chance at it.
        if (isInProperty &&
            (opKind == SyntaxKind::AndSequenceExpr || opKind == SyntaxKind::OrSequenceExpr)) {
            break;
        }

        // see if we should take this operator or if it's part of our parent due to precedence
        int newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        auto opToken = consume();
        auto& right = parseSequenceExpr(newPrecedence, isInProperty);
        left = &factory.binarySequenceExpr(opKind, *left, opToken, right);
    }

    return *left;
}

PropertyExprSyntax& Parser::parseCasePropertyExpr() {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpressionOrDist();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    SmallVector<PropertyCaseItemSyntax*> itemBuffer;
    SourceLocation lastDefault;
    bool errored = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::DefaultKeyword) {
            if (lastDefault && !errored) {
                auto& diag = addDiag(diag::MultipleDefaultCases, peek().location()) << "case"sv;
                diag.addNote(diag::NotePreviousDefinition, lastDefault);
                errored = true;
            }

            lastDefault = peek().location();

            auto def = consume();
            auto colon = consumeIf(TokenKind::Colon);
            auto& expr = parsePropertyExpr(0);
            auto semi = expect(TokenKind::Semicolon);
            itemBuffer.push_back(&factory.defaultPropertyCaseItem(def, colon, expr, semi));
        }
        else if (isPossibleExpression(kind)) {
            Token colon;
            SmallVector<TokenOrSyntax, 8> buffer;
            parseList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpressionOrDist(); });

            auto& expr = parsePropertyExpr(0);
            auto semi = expect(TokenKind::Semicolon);
            itemBuffer.push_back(
                &factory.standardPropertyCaseItem(buffer.copy(alloc), colon, expr, semi));
        }
        else {
            break;
        }
    }

    if (itemBuffer.empty())
        addDiag(diag::CaseStatementEmpty, keyword.location()) << "case"sv;

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return factory.casePropertyExpr(keyword, openParen, condition, closeParen,
                                    itemBuffer.copy(alloc), endcase);
}

PropertyExprSyntax& Parser::parsePropertyPrimary() {
    auto current = peek();
    switch (current.kind) {
        case TokenKind::At: {
            auto event = parseTimingControl();
            SLANG_ASSERT(event);

            // To support clocking events in sampled value system calls,
            // check for an end of an argument and just return if so.
            if (peek(TokenKind::Comma) || peek(TokenKind::CloseParenthesis))
                return factory.clockingPropertyExpr(*event, nullptr);

            // If the parsed property expression *can* be a sequence expression,
            // treat it as one, since that's more permissive.
            auto& propExpr = parsePropertyExpr(0);
            if (propExpr.kind == SyntaxKind::SimplePropertyExpr) {
                SequenceExprSyntax* seqExpr = propExpr.as<SimplePropertyExprSyntax>().expr;
                seqExpr = &factory.clockingSequenceExpr(*event, *seqExpr);
                return factory.simplePropertyExpr(*seqExpr);
            }

            return factory.clockingPropertyExpr(*event, &propExpr);
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto& expr = parsePropertyExpr(0);

            // There is ambiguity between parenthesized property expressions and sequence
            // expressions. We resolve by always rewriting back to a sequence expression
            // if it is possible to do so.
            if (expr.kind == SyntaxKind::SimplePropertyExpr) {
                auto result = &parseParenthesizedSeqExpr(openParen,
                                                         *expr.as<SimplePropertyExprSyntax>().expr);

                // It's possible there is more to the original sequence expression here
                // which we need to manually parse now since property expression parsing will balk
                // at it later.
                if (isBinarySequenceExpression(peek().kind))
                    result = &parseBinarySequenceExpr(result, 0, /* isInProperty */ true);

                return factory.simplePropertyExpr(*result);
            }

            // In a parenthesized property expression a comma is not valid here. However,
            // when parsing a property instance argument, we may be looking at an event
            // expression here. The first term of an event expression may be an `iff`
            // expression that gets parsed as a property expression, and we want to allow
            // a comma separated list of events to follow. AST will disambiguate this
            // later when we learn what kind of expression we're actually being used in.
            Token closeParen;
            auto matchList = parseSequenceMatchList(closeParen);

            return factory.parenthesizedPropertyExpr(openParen, expr, matchList, closeParen);
        }
        case TokenKind::StrongKeyword:
        case TokenKind::WeakKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseSequenceExpr(0, /* isInProperty */ false);
            auto closeParen = expect(TokenKind::CloseParenthesis);
            return factory.strongWeakPropertyExpr(keyword, openParen, expr, closeParen);
        }
        case TokenKind::NotKeyword: {
            auto op = consume();
            auto& expr = parsePropertyPrimary();
            return factory.unaryPropertyExpr(op, expr);
        }
        case TokenKind::NextTimeKeyword:
        case TokenKind::SNextTimeKeyword: {
            auto op = consume();
            if (peek(TokenKind::OpenBracket)) {
                auto openBracket = consume();
                auto selector = parseSequenceRange();
                auto closeBracket = expect(TokenKind::CloseBracket);
                auto& expr = parsePropertyPrimary();

                if (selector && selector->kind != SyntaxKind::BitSelect) {
                    addDiag(diag::InvalidPropertyIndex, selector->sourceRange())
                        << op.valueText() << op.range();
                }

                return factory.unarySelectPropertyExpr(op, openBracket, selector, closeBracket,
                                                       expr);
            }

            auto& expr = parsePropertyPrimary();
            return factory.unaryPropertyExpr(op, expr);
        }
        case TokenKind::AlwaysKeyword:
        case TokenKind::SAlwaysKeyword:
        case TokenKind::EventuallyKeyword:
        case TokenKind::SEventuallyKeyword: {
            auto op = consume();
            if (peek(TokenKind::OpenBracket)) {
                auto openBracket = consume();
                auto selector = parseSequenceRange();
                auto closeBracket = expect(TokenKind::CloseBracket);
                auto& expr = parsePropertyExpr(0);

                if (selector && selector->kind != SyntaxKind::SimpleRangeSelect) {
                    addDiag(diag::InvalidPropertyRange, selector->sourceRange())
                        << op.valueText() << op.range();
                }

                return factory.unarySelectPropertyExpr(op, openBracket, selector, closeBracket,
                                                       expr);
            }

            if (current.kind == TokenKind::SAlwaysKeyword ||
                current.kind == TokenKind::EventuallyKeyword) {
                addDiag(diag::InvalidPropertyRange, op.range()) << op.valueText();
            }

            auto& expr = parsePropertyExpr(0);
            return factory.unaryPropertyExpr(op, expr);
        }
        case TokenKind::AcceptOnKeyword:
        case TokenKind::RejectOnKeyword:
        case TokenKind::SyncAcceptOnKeyword:
        case TokenKind::SyncRejectOnKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpressionOrDist();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& expr = parsePropertyExpr(0);
            return factory.acceptOnPropertyExpr(keyword, openParen, condition, closeParen, expr);
        }
        case TokenKind::IfKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpressionOrDist();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& expr = parsePropertyExpr(0);

            ElsePropertyClauseSyntax* elseClause = nullptr;
            if (peek(TokenKind::ElseKeyword)) {
                auto elseKeyword = consume();
                auto& elseExpr = parsePropertyExpr(0);
                elseClause = &factory.elsePropertyClause(elseKeyword, elseExpr);
            }

            return factory.conditionalPropertyExpr(keyword, openParen, condition, closeParen, expr,
                                                   elseClause);
        }
        case TokenKind::CaseKeyword:
            return parseCasePropertyExpr();
        default: {
            auto& expr = parseSequenceExpr(0, /* isInProperty */ true);
            return factory.simplePropertyExpr(expr);
        }
    }
}

PropertyExprSyntax& Parser::parsePropertyExpr(int precedence) {
    auto dg = setDepthGuard();

    auto left = &parsePropertyPrimary();
    while (true) {
        // either a binary operator, or we're done
        auto opKind = getBinaryPropertyExpr(peek().kind);
        if (opKind == SyntaxKind::Unknown)
            break;

        // see if we should take this operator or if it's part of our parent due to precedence
        int newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        auto opToken = consume();
        auto& right = parsePropertyExpr(newPrecedence);

        // If this could have been an 'and' or 'or' sequence expression, convert it into that
        // instead of continuing with it as a property expression.
        if ((opKind == SyntaxKind::AndPropertyExpr || opKind == SyntaxKind::OrPropertyExpr) &&
            left->kind == SyntaxKind::SimplePropertyExpr &&
            right.kind == SyntaxKind::SimplePropertyExpr) {

            auto& seqExpr = factory.binarySequenceExpr(opKind == SyntaxKind::AndPropertyExpr
                                                           ? SyntaxKind::AndSequenceExpr
                                                           : SyntaxKind::OrSequenceExpr,
                                                       *left->as<SimplePropertyExprSyntax>().expr,
                                                       opToken,
                                                       *right.as<SimplePropertyExprSyntax>().expr);

            left = &factory.simplePropertyExpr(seqExpr);
        }
        else {
            left = &factory.binaryPropertyExpr(opKind, *left, opToken, right);
        }
    }

    return *left;
}

} // namespace slang::parsing
