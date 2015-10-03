#pragma once

namespace slang {

class Lexer;
class BumpAllocator;
class ExpressionSyntax;

class Parser {
public:
    Parser(Lexer& lexer);



private:
    ExpressionSyntax* parseExpression();
    ExpressionSyntax* parseSubExpression(int precedence);
    ExpressionSyntax* parsePrimaryExpression(int precedence);
    ExpressionSyntax* parsePostfixExpression(int precedence);

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);

    void addError(DiagCode code);

    Lexer& lexer;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Token* currentToken;
};

}
