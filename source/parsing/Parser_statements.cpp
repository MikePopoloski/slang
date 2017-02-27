//------------------------------------------------------------------------------
// Parser_statements.cpp
// Statement-related parsing methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Parser.h"

namespace slang {

StatementSyntax& Parser::parseStatement(bool allowEmpty) {
    auto dg = setDepthGuard();

    NamedLabelSyntax* label = nullptr;
    if (peek().kind == TokenKind::Identifier && peek(1).kind == TokenKind::Colon) {
        auto name = consume();
        label = &allocate<NamedLabelSyntax>(name, consume());
    }

    auto attributes = parseAttributes();
    switch (peek().kind) {
        case TokenKind::UniqueKeyword:
        case TokenKind::Unique0Keyword:
        case TokenKind::PriorityKeyword: {
            auto modifier = consume();
            switch (peek().kind) {
                case TokenKind::IfKeyword:
                    return parseConditionalStatement(label, attributes, modifier);
                case TokenKind::CaseKeyword:
                case TokenKind::CaseXKeyword:
                case TokenKind::CaseZKeyword:
                    return parseCaseStatement(label, attributes, modifier, consume());
                default: {
                    addError(DiagCode::ExpectedIfOrCase, peek().location()) << getTokenKindText(modifier.kind);

                    // Construct an empty syntax construct to hold this misplaced token
                    SmallVectorSized<Token, 4> tokens;
                    tokens.append(modifier);

                    SmallVectorSized<Trivia, 8> trivia;
                    trivia.append(Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc)));

                    Token semi = Token::createMissing(alloc, TokenKind::Semicolon, modifier.location());
                    semi = semi.withTrivia(alloc, trivia.copy(alloc));
                    return allocate<EmptyStatementSyntax>(label, attributes, semi);
                }
            }
            break;
        }
        case TokenKind::CaseKeyword:
        case TokenKind::CaseXKeyword:
        case TokenKind::CaseZKeyword:
            return parseCaseStatement(label, attributes, Token(), consume());
        case TokenKind::IfKeyword:
            return parseConditionalStatement(label, attributes, Token());
        case TokenKind::ForeverKeyword: {
            auto forever = consume();
            return allocate<ForeverStatementSyntax>(label, attributes, forever, parseStatement());
        }
        case TokenKind::RepeatKeyword:
        case TokenKind::WhileKeyword:
            return parseLoopStatement(label, attributes);
        case TokenKind::DoKeyword:
            return parseDoWhileStatement(label, attributes);
        case TokenKind::ForKeyword:
            return parseForLoopStatement(label, attributes);
        case TokenKind::ForeachKeyword:
            return parseForeachLoopStatement(label, attributes);
        case TokenKind::ReturnKeyword:
            return parseReturnStatement(label, attributes);
        case TokenKind::BreakKeyword:
        case TokenKind::ContinueKeyword:
            return parseJumpStatement(label, attributes);
        case TokenKind::Hash:
        case TokenKind::DoubleHash:
        case TokenKind::At:
        case TokenKind::AtStar: {
            auto timingControl = parseTimingControl();
            ASSERT(timingControl);
            return allocate<TimingControlStatementSyntax>(label, attributes, *timingControl, parseStatement());
        }
        case TokenKind::AssignKeyword:
            return parseProceduralAssignStatement(label, attributes, SyntaxKind::ProceduralAssignStatement);
        case TokenKind::ForceKeyword:
            return parseProceduralAssignStatement(label, attributes, SyntaxKind::ProceduralForceStatement);
        case TokenKind::DeassignKeyword:
            return parseProceduralDeassignStatement(label, attributes, SyntaxKind::ProceduralDeassignStatement);
        case TokenKind::ReleaseKeyword:
            return parseProceduralDeassignStatement(label, attributes, SyntaxKind::ProceduralReleaseStatement);
        case TokenKind::DisableKeyword:
            return parseDisableStatement(label, attributes);
        case TokenKind::BeginKeyword:
            return parseBlock(SyntaxKind::SequentialBlockStatement, TokenKind::EndKeyword, label, attributes);
        case TokenKind::ForkKeyword:
            return parseBlock(SyntaxKind::ParallelBlockStatement, TokenKind::JoinKeyword, label, attributes);
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword:
            return parseAssertionStatement(label, attributes);
        case TokenKind::RestrictKeyword:
            return parseConcurrentAssertion(label, attributes);
        case TokenKind::ExpectKeyword:
            return parseConcurrentAssertion(label, attributes);
        case TokenKind::WaitKeyword:
            return parseWaitStatement(label, attributes);
        case TokenKind::WaitOrderKeyword:
            return parseWaitOrderStatement(label, attributes);
        case TokenKind::RandCaseKeyword:
            return parseRandCaseStatement(label, attributes);
        case TokenKind::Semicolon:
            if (label)
                addError(DiagCode::NoLabelOnSemicolon, peek().location());
            else if (!allowEmpty)
                addError(DiagCode::ExpectedStatement, peek().location());
            return allocate<EmptyStatementSyntax>(label, attributes, consume());
        case TokenKind::MinusArrow:
        case TokenKind::MinusDoubleArrow:
            return parseEventTriggerStatement(label, attributes);
        default:
            break;
    }

    // everything else should be some kind of expression
    if (isPossibleExpression(peek().kind)) {
        auto& expr = parseExpression();
        return allocate<ExpressionStatementSyntax>(label, attributes, expr, expect(TokenKind::Semicolon));
    }

    addError(DiagCode::ExpectedStatement, peek().location());
    return allocate<EmptyStatementSyntax>(label, attributes, Token());
}

ElseClauseSyntax* Parser::parseElseClause() {
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        return &allocate<ElseClauseSyntax>(elseKeyword, parseStatement());
    }
    return nullptr;
}

ConditionalStatementSyntax& Parser::parseConditionalStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token uniqueOrPriority) {
    auto ifKeyword = expect(TokenKind::IfKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token closeParen;
    auto predicate = parseConditionalPredicate(parseSubExpression(ExpressionOptions::None, 0), TokenKind::CloseParenthesis, closeParen);
    auto statement = parseStatement();
    auto elseClause = parseElseClause();

    return allocate<ConditionalStatementSyntax>(
        label,
        attributes,
        uniqueOrPriority,
        ifKeyword,
        openParen,
        predicate,
        closeParen,
        statement,
        elseClause
    );
}

CaseStatementSyntax& Parser::parseCaseStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token uniqueOrPriority, Token caseKeyword) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& caseExpr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    Token matchesOrInside;
    SmallVectorSized<CaseItemSyntax*, 16> itemBuffer;

    switch (peek().kind) {
        case TokenKind::MatchesKeyword:
            // pattern matching case statement
            matchesOrInside = consume();
            while (true) {
                auto kind = peek().kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(&parseDefaultCaseItem());
                else if (isPossiblePattern(kind)) {
                    auto& pattern = parsePattern();
                    Token tripleAnd;
                    ExpressionSyntax* patternExpr = nullptr;

                    if (peek(TokenKind::TripleAnd)) {
                        tripleAnd = consume();
                        patternExpr = &parseExpression();
                    }

                    auto colon = expect(TokenKind::Colon);
                    itemBuffer.append(&allocate<PatternCaseItemSyntax>(pattern, tripleAnd, patternExpr, colon, parseStatement()));
                }
                else {
                    // no idea what this is; break out and clean up
                    break;
                }
            }
            break;

        case TokenKind::InsideKeyword:
            // range checking case statement
            matchesOrInside = consume();
            while (true) {
                auto kind = peek().kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(&parseDefaultCaseItem());
                else if (isPossibleOpenRangeElement(kind)) {
                    Token colon;
                    SmallVectorSized<TokenOrSyntax, 8> buffer;

                    parseSeparatedList<isPossibleOpenRangeElement, isEndOfCaseItem>(
                        buffer,
                        TokenKind::Colon,
                        TokenKind::Comma,
                        colon,
                        DiagCode::ExpectedOpenRangeElement,
                        [this](bool) { return parseOpenRangeElement(); }
                    );
                    itemBuffer.append(&allocate<StandardCaseItemSyntax>(buffer.copy(alloc), colon, parseStatement()));
                }
                else {
                    // no idea what this is; break out and clean up
                    break;
                }
            }
            break;

        default:
            // normal case statement
            while (true) {
                auto kind = peek().kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(&parseDefaultCaseItem());
                else if (isPossibleExpression(kind)) {
                    Token colon;
                    SmallVectorSized<TokenOrSyntax, 8> buffer;

                    parseSeparatedList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                        buffer,
                        TokenKind::Colon,
                        TokenKind::Comma,
                        colon,
                        DiagCode::ExpectedExpression,
                        [this](bool) { return parseExpression(); }
                    );
                    itemBuffer.append(&allocate<StandardCaseItemSyntax>(buffer.copy(alloc), colon, parseStatement()));
                }
                else {
                    // no idea what this is; break out and clean up
                    break;
                }
            }
            break;
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return allocate<CaseStatementSyntax>(
        label,
        attributes,
        uniqueOrPriority,
        caseKeyword,
        openParen,
        caseExpr,
        closeParen,
        matchesOrInside,
        itemBuffer.copy(alloc),
        endcase);
}

DefaultCaseItemSyntax& Parser::parseDefaultCaseItem() {
    auto defaultKeyword = consume();

    Token colon;
    if (peek(TokenKind::Colon))
        colon = consume();

    return allocate<DefaultCaseItemSyntax>(defaultKeyword, colon, parseStatement());
}

LoopStatementSyntax& Parser::parseLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& statement = parseStatement();
    return allocate<LoopStatementSyntax>(label, attributes, keyword, openParen, expr, closeParen, statement);
}

DoWhileStatementSyntax& Parser::parseDoWhileStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto doKeyword = consume();
    auto& statement = parseStatement();
    auto whileKeyword = expect(TokenKind::WhileKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto semi = expect(TokenKind::Semicolon);
    return allocate<DoWhileStatementSyntax>(label, attributes, doKeyword, statement, whileKeyword, openParen, expr, closeParen, semi);
}

SyntaxNode& Parser::parseForInitializer() {
    if (isVariableDeclaration()) {
        auto varKeyword = consumeIf(TokenKind::VarKeyword);
        auto& type = parseDataType(/* allowImplicit */ false);
        return allocate<ForVariableDeclarationSyntax>(varKeyword, type, parseVariableDeclarator(/* isFirst */ true));
    }
    return parseExpression();
}

ForLoopStatementSyntax& Parser::parseForLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto forKeyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token semi1;
    SmallVectorSized<TokenOrSyntax, 4> initializers;
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfParenList>(
        initializers,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi1,
        DiagCode::ExpectedForInitializer,
        [this](bool) { return parseForInitializer(); }
    );

    auto& stopExpr = parseExpression();
    auto semi2 = expect(TokenKind::Semicolon);

    Token closeParen;
    SmallVectorSized<TokenOrSyntax, 4> steps;
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfParenList>(
        steps,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        closeParen,
        DiagCode::ExpectedExpression,
        [this](bool) { return parseExpression(); }
    );

    return allocate<ForLoopStatementSyntax>(
        label,
        attributes,
        forKeyword,
        openParen,
        initializers.copy(alloc),
        semi1,
        stopExpr,
        semi2,
        steps.copy(alloc),
        closeParen,
        parseStatement()
    );
}

ForeachLoopListSyntax& Parser::parseForeachLoopVariables() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& arrayName = parseName(true);
    ArrayRef<TokenOrSyntax> list;
    Token openBracket;
    Token closeBracket;
    parseSeparatedList<isIdentifierOrComma, isEndOfBracketedList>(
        TokenKind::OpenBracket,
        TokenKind::CloseBracket,
        TokenKind::Comma,
        openBracket,
        list,
        closeBracket,
        DiagCode::ExpectedIdentifier,
        [this](bool) { return parseName(true); }
    );
    auto closeParen = expect(TokenKind::CloseParenthesis);

    return allocate<ForeachLoopListSyntax>(openParen, arrayName, openBracket, list, closeBracket, closeParen);
}

ForeachLoopStatementSyntax& Parser::parseForeachLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto vars = parseForeachLoopVariables();
    return allocate<ForeachLoopStatementSyntax>(
        label,
        attributes,
        keyword,
        vars,
        parseStatement(false)
    );
}

ReturnStatementSyntax& Parser::parseReturnStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    ExpressionSyntax* expr = nullptr;
    if (!peek(TokenKind::Semicolon))
        expr = &parseExpression();

    auto semi = expect(TokenKind::Semicolon);
    return allocate<ReturnStatementSyntax>(label, attributes, keyword, expr, semi);
}

JumpStatementSyntax& Parser::parseJumpStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto semi = expect(TokenKind::Semicolon);
    return allocate<JumpStatementSyntax>(label, attributes, keyword, semi);
}

ProceduralAssignStatementSyntax& Parser::parseProceduralAssignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind) {
    auto keyword = consume();
    auto& lvalue = parsePrimaryExpression();
    auto equals = expect(TokenKind::Equals);
    auto& expr = parseExpression();
    auto semi = expect(TokenKind::Semicolon);
    return allocate<ProceduralAssignStatementSyntax>(kind, label, attributes, keyword, lvalue, equals, expr, semi);
}

ProceduralDeassignStatementSyntax& Parser::parseProceduralDeassignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind) {
    auto keyword = consume();
    auto& variable = parsePrimaryExpression();
    auto semi = expect(TokenKind::Semicolon);
    return allocate<ProceduralDeassignStatementSyntax>(kind, label, attributes, keyword, variable, semi);
}

StatementSyntax& Parser::parseDisableStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto disable = consume();
    if (peek(TokenKind::ForkKeyword)) {
        auto fork = consume();
        return allocate<DisableForkStatementSyntax>(label, attributes, disable, fork, expect(TokenKind::Semicolon));
    }

    auto& name = parseName();
    return allocate<DisableStatementSyntax>(label, attributes, disable, name, expect(TokenKind::Semicolon));
}

StatementSyntax& Parser::parseAssertionStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    // figure out what kind of assertion we're looking at; concurrent assertions
    // are involved and get their own handling
    SyntaxKind assertionKind = SyntaxKind::Unknown;
    TokenKind nextKind = peek(1).kind;
    switch (peek().kind) {
        case TokenKind::AssertKeyword:
            if (nextKind == TokenKind::PropertyKeyword)
                return parseConcurrentAssertion(label, attributes);
            assertionKind = SyntaxKind::ImmediateAssertStatement;
            break;
        case TokenKind::AssumeKeyword:
            if (nextKind == TokenKind::PropertyKeyword)
                return parseConcurrentAssertion(label, attributes);
            assertionKind = SyntaxKind::ImmediateAssumeStatement;
            break;
        case TokenKind::CoverKeyword:
            if (nextKind == TokenKind::PropertyKeyword || nextKind == TokenKind::SequenceKeyword)
                return parseConcurrentAssertion(label, attributes);
            assertionKind = SyntaxKind::ImmediateCoverStatement;
            break;
        default:
            ASSERT(false, "Shouldn't ever get here");
    }

    Token keyword = consume();
    DeferredAssertionSyntax* deferred = nullptr;
    if (peek(TokenKind::Hash)) {
        auto hash = consume();
        auto zero = expect(TokenKind::IntegerLiteral);
        if (!zero.isMissing() && std::get<SVInt>(zero.numericValue()) != 0)
            addError(DiagCode::DeferredDelayMustBeZero, zero.location());
        deferred = &allocate<DeferredAssertionSyntax>(hash, zero, Token());
    }
    else if (peek(TokenKind::FinalKeyword)) {
        deferred = &allocate<DeferredAssertionSyntax>(Token(), Token(), consume());
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto& parenExpr = allocate<ParenthesizedExpressionSyntax>(openParen, expr, expect(TokenKind::CloseParenthesis));
    auto& actionBlock = parseActionBlock();
    return allocate<ImmediateAssertionStatementSyntax>(assertionKind, label, attributes, keyword, deferred, parenExpr, actionBlock);
}

ConcurrentAssertionStatementSyntax& Parser::parseConcurrentAssertion(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    SyntaxKind kind;
    Token propertyOrSequence;
    auto keyword = consume();

    switch (keyword.kind) {
        case TokenKind::AssertKeyword:
            kind = SyntaxKind::AssertPropertyStatement;
            propertyOrSequence = expect(TokenKind::PropertyKeyword);
            break;
        case TokenKind::AssumeKeyword:
            kind = SyntaxKind::AssumePropertyStatement;
            propertyOrSequence = expect(TokenKind::PropertyKeyword);
            break;
        case TokenKind::CoverKeyword:
            if (peek(TokenKind::SequenceKeyword)) {
                kind = SyntaxKind::CoverSequenceStatement;
                propertyOrSequence = consume();
            }
            else {
                kind = SyntaxKind::CoverPropertyStatement;
                propertyOrSequence = expect(TokenKind::PropertyKeyword);
            }
            break;
        case TokenKind::RestrictKeyword:
            kind = SyntaxKind::RestrictPropertyStatement;
            propertyOrSequence = expect(TokenKind::PropertyKeyword);
            break;
        case TokenKind::ExpectKeyword:
            kind = SyntaxKind::ExpectPropertyStatement;
            break;

            DEFAULT_UNREACHABLE;
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto spec = parsePropertySpec();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto action = parseActionBlock();

    return allocate<ConcurrentAssertionStatementSyntax>(kind, label, attributes, keyword, propertyOrSequence, openParen, spec, closeParen, action);
}

PropertySpecSyntax& Parser::parsePropertySpec() {
    TimingControlSyntax* timing = nullptr;
    if (peek(TokenKind::At))
        timing = parseTimingControl();

    DisableIffSyntax* disable = nullptr;
    if (peek(TokenKind::DisableKeyword)) {
        auto keyword = consume();
        auto iff = expect(TokenKind::IffKeyword);
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpressionOrDist();
        disable = &allocate<DisableIffSyntax>(keyword, iff, openParen, expr, expect(TokenKind::CloseParenthesis));
    }
    // TODO: Parse all property expressions
    return allocate<PropertySpecSyntax>(timing, disable, parseExpression());
}

ActionBlockSyntax& Parser::parseActionBlock() {
    StatementSyntax* statement = nullptr;
    ElseClauseSyntax* elseClause = nullptr;

    if (peek(TokenKind::ElseKeyword))
        elseClause = parseElseClause();
    else {
        statement = &parseStatement();
        elseClause = parseElseClause();
    }

    return allocate<ActionBlockSyntax>(statement, elseClause);
}

NamedBlockClauseSyntax* Parser::parseNamedBlockClause() {
    if (peek(TokenKind::Colon)) {
        auto colon = consume();

        // allow the new keyword here to end constructor declarations
        Token name;
        if (peek(TokenKind::NewKeyword))
            name = consume();
        else
            name = expect(TokenKind::Identifier);

        return &allocate<NamedBlockClauseSyntax>(colon, name);
    }
    return nullptr;
}

ArrayRef<SyntaxNode*> Parser::parseBlockItems(TokenKind endKind, Token& end) {
    SmallVectorSized<SyntaxNode*, 16> buffer;
    SmallVectorSized<Token, 8> skipped;
    auto kind = peek().kind;
    bool error = false;

    while (!isEndKeyword(kind) && kind != TokenKind::EndOfFile) {
        SyntaxNode* newNode = nullptr;
        if (isPortDeclaration())
            // TODO: isPortDeclaration doesn't skip over attributes
            newNode = &parsePortDeclaration(parseAttributes());
        else if (isVariableDeclaration())
            newNode = &parseVariableDeclaration(parseAttributes());
        else if (isPossibleStatement(kind))
            newNode = &parseStatement();
        else {
            auto token = consume();
            skipped.append(token);
            if (!error) {
                addError(DiagCode::InvalidTokenInSequentialBlock, token.location());
                error = true;
            }
        }

        if (newNode) {
            buffer.append(prependSkippedTokens(newNode, skipped));
            error = false;
        }
        kind = peek().kind;
    }

    // parallel blocks can end in one of three join keywords
    if (endKind == TokenKind::JoinKeyword) {
        switch (kind) {
            case TokenKind::JoinKeyword:
            case TokenKind::JoinAnyKeyword:
            case TokenKind::JoinNoneKeyword:
                end = consume();
                break;
            default:
                end = expect(endKind);
                break;
        }
    }
    else {
        end = expect(endKind);
    }

    end = prependSkippedTokens(end, skipped);
    return buffer.copy(alloc);
}

BlockStatementSyntax& Parser::parseBlock(SyntaxKind blockKind, TokenKind endKind, NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto begin = consume();
    auto name = parseNamedBlockClause();

    Token end;
    auto items = parseBlockItems(endKind, end);
    auto endName = parseNamedBlockClause();
    return allocate<BlockStatementSyntax>(blockKind, label, attributes, begin, name, items, end, endName);
}

StatementSyntax& Parser::parseWaitStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto wait = consume();
    if (peek(TokenKind::ForkKeyword)) {
        auto fork = consume();
        return allocate<WaitForkStatementSyntax>(label, attributes, wait, fork, expect(TokenKind::Semicolon));
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    return allocate<WaitStatementSyntax>(label, attributes, wait, openParen, expr, closeParen, parseStatement());
}

WaitOrderStatementSyntax& Parser::parseWaitOrderStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    SmallVectorSized<TokenOrSyntax, 4> buffer;

    Token closeParen;
    parseSeparatedList<isIdentifierOrComma, isEndOfParenList>(
        buffer,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        closeParen,
        DiagCode::ExpectedIdentifier,
        [this](bool) { return parseName(); }
    );

    return allocate<WaitOrderStatementSyntax>(
        label,
        attributes,
        keyword,
        openParen,
        buffer.copy(alloc),
        closeParen,
        parseActionBlock()
    );
}

RandCaseStatementSyntax& Parser::parseRandCaseStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto randCase = consume();
    SmallVectorSized<RandCaseItemSyntax*, 16> itemBuffer;

    while (isPossibleExpression(peek().kind)) {
        auto& expr = parseExpression();
        auto colon = expect(TokenKind::Colon);
        itemBuffer.append(&allocate<RandCaseItemSyntax>(expr, colon, parseStatement()));
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return allocate<RandCaseStatementSyntax>(
        label,
        attributes,
        randCase,
        itemBuffer.copy(alloc),
        endcase
    );
}

EventTriggerStatementSyntax& Parser::parseEventTriggerStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto trigger = consume();
    SyntaxKind kind = SyntaxKind::BlockingEventTriggerStatement;
    TimingControlSyntax* timing = nullptr;
    if (trigger.kind == TokenKind::MinusDoubleArrow) {
        kind = SyntaxKind::NonblockingEventTriggerStatement;
        timing = parseTimingControl();
    }
    return allocate<EventTriggerStatementSyntax>(kind, label, attributes, trigger, timing, parseName());
}

}
