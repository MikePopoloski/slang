#pragma once

#include "AllSyntax.h"

namespace slang {

class Lexer;
class BumpAllocator;

class Parser {
public:
    Parser(Lexer& lexer);

    ExpressionSyntax* parseExpression();
    StatementSyntax* parseStatement();

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
    NameSyntax* parseName();
    NameSyntax* parseNamePart();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();
    PatternSyntax* parsePattern();
    EventExpressionSyntax* parseEventExpression();
    TimingControlSyntax* parseTimingControl(bool allowRepeat);
    ConditionalPredicateSyntax* parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token*& end);
    ConditionalPatternSyntax* parseConditionalPattern();
    ConditionalStatementSyntax* parseConditionalStatement(Token* uniqueOrPriority);
    CaseStatementSyntax* parseCaseStatement(Token* uniqueOrPriority, Token* caseKeyword);
    DefaultCaseItemSyntax* parseDefaultCaseItem();
    LoopStatementSyntax* parseLoopStatement();
    DoWhileStatementSyntax* parseDoWhileStatement();
    ReturnStatementSyntax* parseReturnStatement();
    JumpStatementSyntax* parseJumpStatement();
    AssignmentStatementSyntax* parseAssignmentStatement();
    ProceduralAssignStatementSyntax* parseProceduralAssign(SyntaxKind kind);
    ProceduralDeassignStatementSyntax* parseProceduralDeassign(SyntaxKind kind);

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
