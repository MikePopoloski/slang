#pragma once

#include "AllSyntax.h"
#include "TokenWindow.h"

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
    ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();
    PatternSyntax* parsePattern();
    EventExpressionSyntax* parseEventExpression();
    NamedBlockClauseSyntax* parseNamedBlockClause();
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
    ProceduralAssignStatementSyntax* parseProceduralAssignStatement(SyntaxKind kind);
    ProceduralDeassignStatementSyntax* parseProceduralDeassignStatement(SyntaxKind kind);
    StatementSyntax* parseDisableStatement();
    SequentialBlockStatementSyntax* parseSequentialBlock();
    Token* parseSigning();
    VariableDimensionSyntax* parseDimension();
    ArrayRef<VariableDimensionSyntax*> parseDimensionList();
    DataTypeSyntax* parseDataType();

    bool scanTypePart(int& index, TokenKind start, TokenKind end);
    bool isPossibleBlockDeclaration();

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

    Token* peek() { return window.peek(); }
    Token* peek(int offset) { return window.peek(offset); }
    Token* consume() { return window.consume(); }
    Token* consumeIf(TokenKind kind) { return window.consumeIf(kind); }
    Token* expect(TokenKind kind) { return window.expect(kind); }
    bool peek(TokenKind kind) { return window.peek(kind); }

    void addError(DiagCode code);

    Lexer& lexer;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    TokenWindow<&Lexer::lex> window;
    BufferPool<Trivia> triviaPool;
    BufferPool<Token*> tokenPool;
    BufferPool<SyntaxNode*> nodePool;
    BufferPool<TokenOrSyntax> tosPool;
};

}
