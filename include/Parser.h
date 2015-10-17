#pragma once

namespace slang {

class Lexer;
class BumpAllocator;
struct ExpressionSyntax;
struct NameSyntax;
struct ConcatenationExpressionSyntax;
struct StreamingConcatenationExpressionSyntax;
struct StreamExpressionSyntax;
struct ElementSelectSyntax;
struct ArgumentListSyntax;
struct ArgumentSyntax;
struct PatternSyntax;
struct ConditionalPredicateSyntax;
struct ConditionalPatternSyntax;

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
    StreamingConcatenationExpressionSyntax* parseStreamConcatenation(Token* openBrace);
    StreamExpressionSyntax* parseStreamExpression();
    ExpressionSyntax* parseInsideElement();
    ElementSelectSyntax* parseElementSelect();
    NameSyntax* parseNameOrClassHandle();
    NameSyntax* parseScopedName();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();
    PatternSyntax* parsePattern();
    ConditionalPredicateSyntax* parseConditionalPredicate(ExpressionSyntax* first, Token*& question);
    ConditionalPatternSyntax* parseConditionalPattern();

    // helper functions to parse a comma separated list of items
    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        TokenKind openKind,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token*& openToken,
        ArrayRef<TokenOrSyntax>& list,
        Token*& closeToken,
        TParserFunc&& parseItem
    );

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        Buffer<TokenOrSyntax>& buffer,
        TokenKind closeKind,
        TokenKind separatorKind,
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
