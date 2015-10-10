#pragma once

namespace slang {

class Lexer;
class BumpAllocator;
struct ExpressionSyntax;
struct NameSyntax;
struct ConcatenationExpressionSyntax;
struct StreamExpressionSyntax;
struct ElementSelectExpressionSyntax;

class Parser {
public:
    Parser(Lexer& lexer);

    SyntaxNode* parse();
    ExpressionSyntax* parseExpression();

private:
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parseSubExpression(int precedence);
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    SeparatedSyntaxList<StreamExpressionSyntax> parseStreamConcatenation();
    StreamExpressionSyntax* parseStreamExpression();
    ElementSelectExpressionSyntax* parseElementSelect();
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
