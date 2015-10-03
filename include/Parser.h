#pragma once

namespace slang {

class Lexer;
class BumpAllocator;
struct ExpressionSyntax;
struct NameSyntax;
struct ConcatenationExpressionSyntax;
struct StreamExpressionSyntax;

class Parser {
public:
    Parser(Lexer& lexer);



private:
    ExpressionSyntax* parseExpression();
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parseSubExpression(int precedence);
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    SeparatedSyntaxList<StreamExpressionSyntax> parseStreamConcatenation();
    NameSyntax* parseNameOrClassHandle();
    NameSyntax* parseHierarchicalName();
    NameSyntax* parseSimpleName();

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);
    bool peek(TokenKind kind);

    void addError(DiagCode code);

    Lexer& lexer;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Token* currentToken;
    BufferPool<SyntaxNode*> nodePool;
    BufferPool<TokenOrSyntax> tosPool;
};

}
