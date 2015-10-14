#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "StringRef.h"
#include "SourceTracker.h"
#include "Token.h"
#include "Diagnostics.h"
#include "Lexer.h"
#include "Preprocessor.h"
#include "Parser.h"
#include "AllSyntax.h"

namespace {

using namespace slang;

bool isPossibleArgument(TokenKind kind) {
    // allow a comma here to handle cases like:  foo(, 3);
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isEndOfArgumentList(TokenKind kind) {
    return kind == TokenKind::CloseParenthesis || kind == TokenKind::Semicolon;
}

}

namespace slang {

Parser::Parser(Lexer& lexer) :
    lexer(lexer),
    alloc(lexer.getPreprocessor().getAllocator()),
    diagnostics(lexer.getPreprocessor().getDiagnostics()),
    currentToken(nullptr) {
}

SyntaxNode* Parser::parse() {
    return parseExpression();
}

ExpressionSyntax* Parser::parseExpression() {
    return parseSubExpression(0);
}

ExpressionSyntax* Parser::parseMinTypMaxExpression() {
    ExpressionSyntax* first = parseSubExpression(0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto typ = parseSubExpression(0);
    auto colon2 = expect(TokenKind::Colon);
    auto max = parseSubExpression(0);

    return alloc.emplace<MinTypMaxExpressionSyntax>(first, colon1, typ, colon2, max);
}

ExpressionSyntax* Parser::parseSubExpression(int precedence) {
    ExpressionSyntax* leftOperand = nullptr;
    int newPrecedence = 0;

    auto current = peek();
    if (current->kind == TokenKind::TaggedKeyword) {
        // TODO: check for trailing expression
        auto tagged = consume();
        auto member = expect(TokenKind::Identifier);
        return alloc.emplace<TaggedUnionExpressionSyntax>(tagged, member, nullptr);
    }

    SyntaxKind opKind = getUnaryPrefixExpression(current->kind);
    if (opKind != SyntaxKind::Unknown) {
        auto opToken = consume();

        newPrecedence = getPrecedence(opKind);
        ExpressionSyntax* operand = parseSubExpression(newPrecedence);
        leftOperand = alloc.emplace<PrefixUnaryExpressionSyntax>(opKind, opToken, operand);
    }
    else {
        // not a unary operator, so must be a primary expression
        leftOperand = parsePrimaryExpression();
    }

    while (true) {
        // either a binary operator, or we're done
        current = peek();
        opKind = getBinaryExpression(current->kind);
        if (opKind == SyntaxKind::Unknown)
            break;

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
            auto rightOperand = parseSubExpression(newPrecedence);
            leftOperand = alloc.emplace<BinaryExpressionSyntax>(opKind, leftOperand, opToken, rightOperand);
        }
    }

    // see if we have a conditional operator we want to take


    return leftOperand;
}

ExpressionSyntax* Parser::parsePrimaryExpression() {
    ExpressionSyntax* expr;
    TokenKind kind = peek()->kind;
    switch (kind) {
        case TokenKind::StringLiteral:
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::NullKeyword:
        case TokenKind::Dollar: {
            auto literal = consume();
            expr = alloc.emplace<LiteralExpressionSyntax>(getLiteralExpression(literal->kind), literal);
            break;
        }
        case TokenKind::SystemIdentifier: {
            auto identifier = consume();
            expr = alloc.emplace<KeywordNameSyntax>(SyntaxKind::SystemName, identifier);
            break;
        }
        case TokenKind::LocalKeyword: {
            auto keyword = consume();
            auto doubleColon = expect(TokenKind::DoubleColon);

            expr = alloc.emplace<ScopedNameSyntax>(
                alloc.emplace<KeywordNameSyntax>(SyntaxKind::LocalScope, keyword),
                doubleColon,
                parseNameOrClassHandle()
            );
            break;
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            expr = parseMinTypMaxExpression();

            auto closeParen = expect(TokenKind::CloseParenthesis);
            expr = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, expr, closeParen);
            break;
        }
        case TokenKind::OpenBrace: {
            // several different things this could be:
            // 1. empty queue expression { }
            // 2. streaming concatenation {>> {expr}}
            // 3. multiple concatenation {expr {concat}}
            // 4. concatenation {expr, expr}
            auto openBrace = consume();
            switch (peek()->kind) {
                case TokenKind::CloseBrace:
                    expr = alloc.emplace<EmptyQueueExpressionSyntax>(openBrace, consume());
                    break;
                case TokenKind::LeftShift:
                case TokenKind::RightShift: {
                    auto op = consume();
                    ExpressionSyntax* sliceSize = nullptr;
                    if (!peek(TokenKind::OpenBrace))
                        sliceSize = parseExpression();

                    auto openBraceInner = expect(TokenKind::OpenBrace);
                    auto concat = parseStreamConcatenation();
                    auto closeBraceInner = expect(TokenKind::CloseBrace);
                    auto closeBrace = expect(TokenKind::CloseBrace);

                    expr = alloc.emplace<StreamingConcatenationExpressionSyntax>(
                        openBrace,
                        op,
                        sliceSize,
                        openBraceInner,
                        concat,
                        closeBraceInner, 
                        closeBrace
                    );
                    break;
                }
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
        default: {
            // might be a variable name or class handle expression
            expr = parseNameOrClassHandle();
            if (expr)
                break;

            // TODO: error
            auto missing = Token::missing(alloc, TokenKind::Identifier);
            expr = alloc.emplace<IdentifierNameSyntax>(missing);
            break;
        }
    }

    return parsePostfixExpression(expr);
}

ExpressionSyntax* Parser::parseInsideExpression(ExpressionSyntax* expr) {
    auto inside = expect(TokenKind::InsideKeyword);
    auto openBrace = expect(TokenKind::OpenBrace);

    auto buffer = tosPool.get();
    while (!peek(TokenKind::CloseParenthesis)) {
        if (!peek(TokenKind::OpenBracket))
            buffer.append(parseExpression());
        else
            buffer.append(parseElementSelect());

        // TODO: rework this for error handling
        if (!peek(TokenKind::Comma))
            break;

        buffer.append(consume());
    }

    auto closeBrace = expect(TokenKind::CloseBrace);
    return alloc.emplace<InsideExpressionSyntax>(expr, inside, openBrace, buffer.copy(alloc), closeBrace);
}

ConcatenationExpressionSyntax* Parser::parseConcatenation(Token* openBrace, ExpressionSyntax* first) {
    auto buffer = tosPool.get();
    if (first)
        buffer.append(first);
    else
        buffer.append(parseExpression());

    while (peek(TokenKind::Comma)) {
        buffer.append(consume());
        buffer.append(parseExpression());
    }

    auto closeBrace = expect(TokenKind::CloseBrace);
    return alloc.emplace<ConcatenationExpressionSyntax>(openBrace, buffer.copy(alloc), closeBrace);
}



SeparatedSyntaxList<StreamExpressionSyntax> Parser::parseStreamConcatenation() {
    auto buffer = tosPool.get();

    // TODO: parse stream expression instead of expression
    buffer.append(parseStreamExpression());

    while (peek(TokenKind::Comma)) {
        buffer.append(consume());
        buffer.append(parseStreamExpression());
    }

    return buffer.copy(alloc);
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

ElementSelectSyntax* Parser::parseElementSelect() {
    auto openBracket = expect(TokenKind::OpenBracket);
    auto expr = parseExpression();

    SelectorSyntax* selector;
    switch (peek()->kind) {
        case TokenKind::Colon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::SimpleRangeSelect, expr, range, parseExpression());
            break;
        }
        case TokenKind::PlusColon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::AscendingRangeSelect, expr, range, parseExpression());
            break;
        }
        case TokenKind::MinusColon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::DescendingRangeSelect, expr, range, parseExpression());
            break;
        }
        default:
            selector = alloc.emplace<BitSelectSyntax>(expr);
            break;
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return alloc.emplace<ElementSelectSyntax>(openBracket, selector, closeBracket);
}

ExpressionSyntax* Parser::parsePostfixExpression(ExpressionSyntax* expr) {
    while (true) {
        switch (peek()->kind) {
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
                expr = alloc.emplace<InvocationExpressionSyntax>(expr, parseArgumentList());
                break;
            case TokenKind::DoublePlus:
                // can't have any other postfix expressions after inc/dec
                return alloc.emplace<PostfixUnaryExpressionSyntax>(SyntaxKind::PostincrementExpression, expr, consume());
            case TokenKind::DoubleMinus:
                // can't have any other postfix expressions after inc/dec
                return alloc.emplace<PostfixUnaryExpressionSyntax>(SyntaxKind::PostdecrementExpression, expr, consume());
            default:
                return expr;
        }
    }
}

NameSyntax* Parser::parseNameOrClassHandle() {
    switch (peek()->kind) {
        case TokenKind::UnitSystemName: {
            auto unit = consume();
            auto separator = expect(TokenKind::DoubleColon);

            return alloc.emplace<ScopedNameSyntax>(
                alloc.emplace<KeywordNameSyntax>(SyntaxKind::UnitScope, unit),
                separator,
                parseScopedName()
            );
        }
        case TokenKind::Identifier:
            return parseScopedName();
        case TokenKind::ThisKeyword:
            return alloc.emplace<KeywordNameSyntax>(SyntaxKind::ThisHandle, consume());
        case TokenKind::SuperKeyword:
            return alloc.emplace<KeywordNameSyntax>(SyntaxKind::SuperHandle, consume());
        default:
            return nullptr;
    }
}

NameSyntax* Parser::parseScopedName() {
    if (peek(TokenKind::RootSystemName))
        return alloc.emplace<KeywordNameSyntax>(SyntaxKind::RootScope, consume());

    NameSyntax* left;
    auto identifier = expect(TokenKind::Identifier);
    if (!peek(TokenKind::Hash))
        left = alloc.emplace<IdentifierNameSyntax>(identifier);
    else {
        auto hash = consume();
        auto parameterValues = alloc.emplace<ParameterValueAssignmentSyntax>(hash, parseArgumentList());
        left = alloc.emplace<ClassNameSyntax>(identifier, parameterValues);
    }

    if (!peek(TokenKind::DoubleColon))
        return left;
    
    auto doubleColon = consume();
    return alloc.emplace<ScopedNameSyntax>(left, doubleColon, parseScopedName());
}

ArgumentListSyntax* Parser::parseArgumentList() {
    Token* openParen;
    Token* closeParen;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseCommaSeparatedList<isPossibleArgument, isEndOfArgumentList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        openParen,
        list,
        closeParen,
        &Parser::parseArgument
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

// this is a generalized method for parsing a comma separated list of things
// with bookend tokens in a way that robustly handles bad tokens
template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
void Parser::parseCommaSeparatedList(
    TokenKind openKind,
    TokenKind closeKind,
    Token*& openToken,
    ArrayRef<TokenOrSyntax>& list,
    Token*& closeToken,
    TParserFunc&& parseItem
    ) {
    Trivia skippedTokens;
    openToken = expect(openKind);

    auto buffer = tosPool.get();
    auto current = peek();
    if (!IsEnd(current->kind)) {
        while (true) {
            if (IsExpected(current->kind)) {
                buffer.append(prependTrivia((this->*parseItem)(), &skippedTokens));
                while (true) {
                    current = peek();
                    if (IsEnd(current->kind))
                        break;

                    if (IsExpected(current->kind)) {
                        buffer.append(prependTrivia(expect(TokenKind::Comma), &skippedTokens));
                        buffer.append((this->*parseItem)());
                        continue;
                    }

                    if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens) == SkipAction::Abort)
                        break;
                }
                // found the end
                break;
            }
            else if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens) == SkipAction::Abort)
                break;
            else
                current = peek();
        }
    }
    closeToken = prependTrivia(expect(closeKind), &skippedTokens);
    list = buffer.copy(alloc);
}

template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
Parser::SkipAction Parser::skipBadTokens(Trivia* skippedTokens) {
    auto tokens = tokenPool.get();
    auto result = SkipAction::Continue;
    while (!IsExpected(peek()->kind)) {
        if (IsAbort(peek()->kind)) {
            result = SkipAction::Abort;
            break;
        }
        tokens.append(consume());
    }

    if (tokens.empty())
        *skippedTokens = Trivia();
    else
        *skippedTokens = Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc));

    return result;
}

SyntaxNode* Parser::prependTrivia(SyntaxNode* node, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && node)
        prependTrivia(node->getFirstToken(), trivia);
    return node;
}

Token* Parser::prependTrivia(Token* token, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && token) {
        auto buffer = triviaPool.get();
        buffer.append(*trivia);
        buffer.appendRange(token->trivia);
        token->trivia = buffer.copy(alloc);

        *trivia = Trivia();
    }
    return token;
}

void Parser::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

bool Parser::peek(TokenKind kind) {
    return peek()->kind == kind;
}

Token* Parser::peek() {
    if (!currentToken)
        currentToken = lexer.lex();
    return currentToken;
}

Token* Parser::consume() {
    Token* result = peek();
    currentToken = nullptr;
    return result;
}

Token* Parser::expect(TokenKind kind) {
    if (peek()->kind == kind)
        return consume();

    return Token::missing(alloc, kind);
}

}