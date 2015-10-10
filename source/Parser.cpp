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

ParameterValueAssignmentSyntax* Parser::parseParameterValueAssignment() {
    auto hash = expect(TokenKind::Hash);
    auto openParen = expect(TokenKind::OpenParenthesis);

    auto buffer = tosPool.get();
    while (!peek(TokenKind::CloseParenthesis)) {
        if (!peek(TokenKind::Dot))
            buffer.append(alloc.emplace<OrderedParameterAssignmentSyntax>(parseParamExpression())); 
        else {
            auto dot = consume();
            auto name = expect(TokenKind::Identifier);
            auto innerOpenParen = expect(TokenKind::OpenParenthesis);

            ExpressionSyntax* expr = nullptr;
            if (!peek(TokenKind::CloseParenthesis))
                expr = parseParamExpression();

            buffer.append(alloc.emplace<NamedParameterAssignmentSyntax>(dot, name, innerOpenParen, expr, expect(TokenKind::CloseParenthesis)));
        }

        // TODO: rework this for error handling
        if (!peek(TokenKind::Comma))
            break;

        buffer.append(consume());
    }

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return alloc.emplace<ParameterValueAssignmentSyntax>(hash, openParen, buffer.copy(alloc), closeParen);
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

ExpressionSyntax* Parser::parseParamExpression() {
    // TODO: this could also be a data type
    return parseExpression();
}

ExpressionSyntax* Parser::parseSubExpression(int precedence) {
    ExpressionSyntax* leftOperand = nullptr;
    int newPrecedence = 0;

    auto current = peek();
    SyntaxKind opKind = getUnaryExpression(current->kind);
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
        auto opToken = consume();

        auto rightOperand = parseSubExpression(newPrecedence);
        leftOperand = alloc.emplace<BinaryExpressionSyntax>(opKind, leftOperand, opToken, rightOperand);
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

            expr = alloc.emplace<HierarchicalNameSyntax>(
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

            // TODO: explicitly check for misplaced :: to give a better error
            if (kind == TokenKind::DoubleColon) {
            }

            // TODO: error
            auto missing = Token::missing(alloc, TokenKind::Identifier);
            expr = alloc.emplace<IdentifierNameSyntax>(missing);
            break;
        }
    }

    return parsePostfixExpression(expr);
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

ElementSelectExpressionSyntax* Parser::parseElementSelect() {
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
    return alloc.emplace<ElementSelectExpressionSyntax>(openBracket, selector, closeBracket);
}

ExpressionSyntax* Parser::parsePostfixExpression(ExpressionSyntax* expr) {
    return expr;
}

NameSyntax* Parser::parseNameOrClassHandle() {
    switch (peek()->kind) {
        case TokenKind::UnitSystemName: {
            auto unit = consume();
            auto separator = expect(TokenKind::DoubleColon);

            return alloc.emplace<HierarchicalNameSyntax>(
                alloc.emplace<KeywordNameSyntax>(SyntaxKind::UnitScope, unit),
                separator,
                parseHierarchicalName()
            );
        }
        case TokenKind::RootSystemName:
        case TokenKind::Identifier:
            return parseHierarchicalName();
        case TokenKind::ThisKeyword:
            return alloc.emplace<KeywordNameSyntax>(SyntaxKind::ThisHandle, consume());
        case TokenKind::SuperKeyword:
            return alloc.emplace<KeywordNameSyntax>(SyntaxKind::SuperHandle, consume());
        default:
            return nullptr;
    }
}

NameSyntax* Parser::parseHierarchicalName() {
    NameSyntax* left;
    if (peek(TokenKind::RootSystemName))
        left = alloc.emplace<KeywordNameSyntax>(SyntaxKind::RootScope, consume());
    else {
        auto identifier = expect(TokenKind::Identifier);
        if (peek(TokenKind::Hash))
            left = alloc.emplace<ClassNameSyntax>(identifier, parseParameterValueAssignment());
        else
            left = alloc.emplace<IdentifierNameSyntax>(identifier);
    }

    switch (peek()->kind) {
        case TokenKind::DoubleColon: {
            // TODO: can't transition from dots back to double colon; error if we see that and pretend they used a dot
            auto doubleColon = consume();
            return alloc.emplace<HierarchicalNameSyntax>(left, doubleColon, parseHierarchicalName());
        }
        case TokenKind::Dot: {
            auto dot = consume();
            return alloc.emplace<HierarchicalNameSyntax>(left, dot, parseHierarchicalName());
        }
        default:
            return left;
    }
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