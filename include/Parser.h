#pragma once

#include "AllSyntax.h"

namespace slang {

class BumpAllocator;

class Parser {
public:
    Parser(Preprocessor& preprocessor);

    CompilationUnitSyntax* parseCompilationUnit();

    ExpressionSyntax* parseExpression();
    StatementSyntax* parseStatement();
    ModuleDeclarationSyntax* parseModule();

private:    
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parseInsideExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    StreamingConcatenationExpressionSyntax* parseStreamConcatenation(Token* openBrace);
    StreamExpressionSyntax* parseStreamExpression();
    ExpressionSyntax* parseInsideElement();
    ElementSelectSyntax* parseElementSelect();
    SelectorSyntax* parseElementSelector();
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
    ConditionalStatementSyntax* parseConditionalStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority);
    CaseStatementSyntax* parseCaseStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority, Token* caseKeyword);
    DefaultCaseItemSyntax* parseDefaultCaseItem();
    LoopStatementSyntax* parseLoopStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    DoWhileStatementSyntax* parseDoWhileStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ForLoopStatementSyntax* parseForLoopStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ForInitializerSyntax* parseForInitializer();
    ReturnStatementSyntax* parseReturnStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    JumpStatementSyntax* parseJumpStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    AssignmentStatementSyntax* parseAssignmentStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ProceduralAssignStatementSyntax* parseProceduralAssignStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    ProceduralDeassignStatementSyntax* parseProceduralDeassignStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    StatementSyntax* parseDisableStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    SequentialBlockStatementSyntax* parseSequentialBlock(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    Token* parseSigning();
    VariableDimensionSyntax* parseDimension();
    ArrayRef<VariableDimensionSyntax*> parseDimensionList();
    StructUnionTypeSyntax* parseStructUnion(SyntaxKind syntaxKind);
    EnumTypeSyntax* parseEnum();
    DataTypeSyntax* parseDataType(bool allowImplicit);
    DotMemberClauseSyntax* parseDotMemberClause();
    ArrayRef<AttributeInstanceSyntax*> parseAttributes();
    AttributeSpecSyntax* parseAttributeSpec();
    ModuleHeaderSyntax* parseModuleHeader();
    ModuleDeclarationSyntax* parseModule(ArrayRef<AttributeInstanceSyntax*> attributes);
    NonAnsiPortSyntax* parseNonAnsiPort();
    AnsiPortSyntax* parseAnsiPort();
    PortHeaderSyntax* parsePortHeader(Token* direction);
    PortDeclarationSyntax* parsePortDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseMember();
    ArrayRef<MemberSyntax*> parseMemberList(TokenKind endKind, Token*& endToken);
    TimeUnitsDeclarationSyntax* parseTimeUnitsDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    ArrayRef<PackageImportDeclarationSyntax*> parsePackageImports();
    PackageImportItemSyntax* parsePackageImportItem();
    ParameterPortDeclarationSyntax* parseParameterPort();
    MemberSyntax* parseVariableDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseNetDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchyInstantiationSyntax* parseHierarchyInstantiation(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchicalInstanceSyntax* parseHierarchicalInstance();
    PortConnectionSyntax* parsePortConnection();

    bool isPortDeclaration();
    bool isNetDeclaration();
    bool isVariableDeclaration();
    bool isHierarchyInstantiation();
    bool isNonAnsiPort();
    bool isPlainPortName();
    bool scanDimensionList(int& index);

    template<bool AllowPatternMatch>
    ExpressionSyntax* parseSubExpression(int precedence);

    template<bool(*IsEnd)(TokenKind)>
    ArrayRef<TokenOrSyntax> parseVariableDeclarators(TokenKind endKind, Token*& end);

    template<bool AllowMinTypMax>
    VariableDeclaratorSyntax* parseVariableDeclarator(bool isFirst);

    template<bool AllowMinTypeMax>
    ExpressionSyntax* parseAssignmentExpression();

    template<bool(*IsEnd)(TokenKind)>
    bool scanTypePart(int& index, TokenKind start, TokenKind end);

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

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedListWithFirst(
        Buffer<TokenOrSyntax>& buffer,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token*& closeToken,
        TParserFunc&& parseItem
    );

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedListWithFirst(
        Buffer<TokenOrSyntax>& buffer,
        TokenKind separatorKind,
        Trivia* skippedTokens,
        TParserFunc&& parseItem
    );

	enum class SkipAction {
		Continue,
		Abort
	};

	void reduceSkippedTokens(Buffer<Token*>& skipped, Buffer<Trivia>& trivia);

    template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
    SkipAction skipBadTokens(Trivia* skippedTokens);

    template<typename T>
    void prependTrivia(ArrayRef<T*> list, Trivia* trivia);

	SyntaxNode* prependTrivia(SyntaxNode* node, Trivia* trivia);
    Token* prependTrivia(Token* token, Trivia* trivia);

	void prependTrivia(SyntaxNode* node, Buffer<Trivia>& trivia);
	Token* prependTrivia(Token* token, Buffer<Trivia>& trivia);

	SyntaxNode* prependSkippedTokens(SyntaxNode* node, Buffer<Token*>& tokens);
	Token* prependSkippedTokens(Token* node, Buffer<Token*>& tokens);

    void addError(DiagCode code);

	Token* peek(int offset);
	Token* peek();
	bool peek(TokenKind kind);
	Token* consume();
	Token* consumeIf(TokenKind kind);
	Token* expect(TokenKind kind);

	// sliding window of tokens
	class Window {
	public:
		explicit Window(Preprocessor& source) :
			tokenSource(source)
		{
			capacity = 32;
			buffer = new Token*[capacity];
		}

		~Window() { delete[] buffer; }

		Window(const Window&) = delete;
		Window& operator=(const Window&) = delete;

		Preprocessor& tokenSource;
		Token** buffer = nullptr;
		Token* currentToken = nullptr;
		int currentOffset = 0;
		int count = 0;
		int capacity = 0;

		void addNew();
		void moveToNext();
	};

	Window window;
    BumpAllocator& alloc;
    BufferPool<Trivia> triviaPool;
    BufferPool<Token*> tokenPool;
    BufferPool<SyntaxNode*> nodePool;
    BufferPool<TokenOrSyntax> tosPool;
};

}
