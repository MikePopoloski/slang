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

ExpressionSyntax* Parser::parseExpression() {
    return parseSubExpression(0);
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
        leftOperand = parsePrimaryExpression(precedence);
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

ExpressionSyntax* Parser::parsePrimaryExpression(int precedence) {
    // first try to get a class name or handle expression
    //ExpressionSyntax expr = ParseNameOrClassHandle();
    //if (expr == null) {



    ExpressionSyntax* expr = nullptr;
    //switch (peek()->kind) {
    //    case TokenKind::StringLiteral:
    //    case TokenKind::IntegerLiteral:
    //    case TokenKind::RealLiteral:
    //    case TokenKind::TimeLiteral:
    //    case TokenKind::NullKeyword:
    //        auto literal = consume();
    //        expr = alloc.emplace<LiteralExpressionSyntax>(getLiteralExpression(literal->kind), literal);
    //        break;
    //    case TokenKind::SystemIdentifier:
    //        auto identifier = consume();
    //        expr = alloc.emplace<KeywordNameSyntax>(SyntaxKind::SystemName, identifier);
    //        break;
    //    case TokenKind::LocalKeyword:
    //        Token keyword;
    //        source.Consume(out keyword);

    //        Token doubleColon;
    //        Expect(TokenKind::DoubleColon, out doubleColon);
    //        expr = new HierarchicalNameSyntax(
    //            new KeywordNameSyntax(SyntaxKind.LocalScope, ref keyword),
    //            ref doubleColon,
    //            ParseNameOrClassHandle()
    //            );
    //        break;
    //    case TokenKind::DoubleColon:
    //        // misplaced ::
    //        // TODO: error
    //        goto default;
    //    case TokenKind::OpenParenthesis:
    //        Token openParen;
    //        source.Consume(out openParen);
    //        expr = ParseExpression();

    //        Token closeParen;
    //        Expect(TokenKind::CloseParenthesis, out closeParen);
    //        expr = new ParenthesizedExpressionSyntax(ref openParen, expr, ref closeParen);
    //        break;
    //    default:
    //        // TODO: error
    //        var missing = Token.Missing(TokenKind.Identifier);
    //        expr = new IdentifierNameSyntax(ref missing);
    //        break;
    //}

    return parsePostfixExpression(expr);
}

ExpressionSyntax* Parser::parsePostfixExpression(ExpressionSyntax* expr) {
    return expr;
}

void Parser::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
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