#pragma once

namespace slang {

class Lexer;
class BumpAllocator;
struct ExpressionSyntax;
struct NameSyntax;
struct ConcatenationExpressionSyntax;
struct StreamExpressionSyntax;
struct ElementSelectSyntax;
struct ArgumentListSyntax;

class Parser {
public:
    Parser(Lexer& lexer);

    SyntaxNode* parse();
    ExpressionSyntax* parseExpression();

private:
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parseSubExpression(int precedence);
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parseParamExpression();
    ExpressionSyntax* parseInsideExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    SeparatedSyntaxList<StreamExpressionSyntax> parseStreamConcatenation();
    StreamExpressionSyntax* parseStreamExpression();
    ElementSelectSyntax* parseElementSelect();
    NameSyntax* parseNameOrClassHandle();
    NameSyntax* parseScopedName();
    ArgumentListSyntax* parseArgumentList();

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
