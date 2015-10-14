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
struct ArgumentSyntax;

class Parser {
public:
    Parser(Lexer& lexer);

    SyntaxNode* parse();
    ExpressionSyntax* parseExpression();

private:
    enum class SkipAction {
        Continue,
        Abort
    };
    
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parseSubExpression(int precedence);
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parseInsideExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    SeparatedSyntaxList<StreamExpressionSyntax> parseStreamConcatenation();
    StreamExpressionSyntax* parseStreamExpression();
    ElementSelectSyntax* parseElementSelect();
    NameSyntax* parseNameOrClassHandle();
    NameSyntax* parseScopedName();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseCommaSeparatedList(
        TokenKind openKind,
        TokenKind closeKind,
        Token*& openToken,
        ArrayRef<TokenOrSyntax>& list,
        Token*& closeToken,
        TParserFunc&& parseItem
    );

    template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
    SkipAction skipBadTokens(Trivia* skippedTokens);

    SyntaxNode* prependTrivia(SyntaxNode* node, Trivia* trivia);
    Token* prependTrivia(Token* token, Trivia* trivia);

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);
    bool peek(TokenKind kind);

    void addError(DiagCode code);

    Lexer& lexer;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Token* currentToken;
    BufferPool<Trivia> triviaPool;
    BufferPool<Token*> tokenPool;
    BufferPool<SyntaxNode*> nodePool;
    BufferPool<TokenOrSyntax> tosPool;
};

}
