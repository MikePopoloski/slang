//------------------------------------------------------------------------------
// Parser_statements.cpp
// Statement-related parsing methods
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/parsing/Parser.h"

namespace slang {

StatementSyntax& Parser::parseStatement(bool allowEmpty) {
    auto dg = setDepthGuard();

    NamedLabelSyntax* label = nullptr;
    if (peek().kind == TokenKind::Identifier && peek(1).kind == TokenKind::Colon) {
        auto name = consume();
        label = &factory.namedLabel(name, consume());
    }

    auto attributes = parseAttributes();
    switch (peek().kind) {
        case TokenKind::UniqueKeyword:
        case TokenKind::Unique0Keyword:
        case TokenKind::PriorityKeyword: {
            switch (peek(1).kind) {
                case TokenKind::IfKeyword:
                    return parseConditionalStatement(label, attributes, consume());
                case TokenKind::CaseKeyword:
                case TokenKind::CaseXKeyword:
                case TokenKind::CaseZKeyword: {
                    auto modifier = consume();
                    return parseCaseStatement(label, attributes, modifier, consume());
                }
                default: {
                    addDiag(diag::ExpectedIfOrCase, peek(1).location())
                        << LexerFacts::getTokenKindText(peek().kind);
                    skipToken(std::nullopt);
                    return factory.emptyStatement(
                        label, attributes, missingToken(TokenKind::Semicolon, peek().location()));
                }
            }
        }
        case TokenKind::CaseKeyword:
        case TokenKind::CaseXKeyword:
        case TokenKind::CaseZKeyword:
            return parseCaseStatement(label, attributes, Token(), consume());
        case TokenKind::IfKeyword:
            return parseConditionalStatement(label, attributes, Token());
        case TokenKind::ForeverKeyword: {
            auto forever = consume();
            return factory.foreverStatement(label, attributes, forever, parseStatement());
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
        case TokenKind::At: {
            auto timingControl = parseTimingControl(/* isSequenceExpr */ false);
            ASSERT(timingControl);
            return factory.timingControlStatement(label, attributes, *timingControl,
                                                  parseStatement());
        }
        case TokenKind::AssignKeyword:
            return parseProceduralAssignStatement(label, attributes,
                                                  SyntaxKind::ProceduralAssignStatement);
        case TokenKind::ForceKeyword:
            return parseProceduralAssignStatement(label, attributes,
                                                  SyntaxKind::ProceduralForceStatement);
        case TokenKind::DeassignKeyword:
            return parseProceduralDeassignStatement(label, attributes,
                                                    SyntaxKind::ProceduralDeassignStatement);
        case TokenKind::ReleaseKeyword:
            return parseProceduralDeassignStatement(label, attributes,
                                                    SyntaxKind::ProceduralReleaseStatement);
        case TokenKind::DisableKeyword:
            return parseDisableStatement(label, attributes);
        case TokenKind::BeginKeyword:
            return parseBlock(SyntaxKind::SequentialBlockStatement, TokenKind::EndKeyword, label,
                              attributes);
        case TokenKind::ForkKeyword:
            return parseBlock(SyntaxKind::ParallelBlockStatement, TokenKind::JoinKeyword, label,
                              attributes);
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword:
            return parseAssertionStatement(label, attributes);
        case TokenKind::RestrictKeyword:
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
                addDiag(diag::NoLabelOnSemicolon, peek().location());
            else if (!allowEmpty)
                addDiag(diag::ExpectedStatement, peek().location());
            return factory.emptyStatement(label, attributes, consume());
        case TokenKind::MinusArrow:
        case TokenKind::MinusDoubleArrow:
            return parseEventTriggerStatement(label, attributes);
        case TokenKind::VoidKeyword:
            return parseVoidCallStatement(label, attributes);
        default:
            break;
    }

    // everything else should be some kind of expression
    if (isPossibleExpression(peek().kind)) {
        auto& expr = parseSubExpression(ExpressionOptions::ProceduralAssignmentContext, 0);
        return factory.expressionStatement(label, attributes, expr, expect(TokenKind::Semicolon));
    }

    addDiag(diag::ExpectedStatement, peek().location());
    return factory.emptyStatement(label, attributes,
                                  missingToken(TokenKind::Semicolon, peek().location()));
}

ElseClauseSyntax* Parser::parseElseClause() {
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        return &factory.elseClause(elseKeyword, parseStatement());
    }
    return nullptr;
}

ConditionalStatementSyntax& Parser::parseConditionalStatement(NamedLabelSyntax* label,
                                                              AttrList attributes,
                                                              Token uniqueOrPriority) {
    auto ifKeyword = expect(TokenKind::IfKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token closeParen;
    auto& predicate =
        parseConditionalPredicate(parseExpression(), TokenKind::CloseParenthesis, closeParen);
    auto& statement = parseStatement();
    auto elseClause = parseElseClause();

    return factory.conditionalStatement(label, attributes, uniqueOrPriority, ifKeyword, openParen,
                                        predicate, closeParen, statement, elseClause);
}

template<typename IsItemFunc, typename ParseItemFunc>
bool Parser::parseCaseItems(TokenKind caseKind, SmallVector<CaseItemSyntax*>& itemBuffer,
                            IsItemFunc&& isItem, ParseItemFunc&& parseItem) {
    SourceLocation lastDefault;
    bool errored = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::DefaultKeyword) {
            if (lastDefault && !errored) {
                auto& diag = addDiag(diag::MultipleDefaultCases, peek().location());
                diag << LexerFacts::getTokenKindText(caseKind);
                diag.addNote(diag::NotePreviousDefinition, lastDefault);
                errored = true;
            }

            lastDefault = peek().location();
            itemBuffer.append(&parseDefaultCaseItem());
        }
        else if (isItem(kind)) {
            itemBuffer.append(parseItem());
        }
        else if (kind == TokenKind::EndOfFile || isEndKeyword(kind)) {
            break;
        }
        else {
            // no idea what this is; skip it
            skipToken(errored ? std::nullopt : std::make_optional(diag::ExpectedCaseItem));
            errored = true;
        }
    }

    return errored;
}

CaseStatementSyntax& Parser::parseCaseStatement(NamedLabelSyntax* label, AttrList attributes,
                                                Token uniqueOrPriority, Token caseKeyword) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& caseExpr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    Token matchesOrInside;
    SmallVectorSized<CaseItemSyntax*, 16> itemBuffer;
    bool errored = false;

    switch (peek().kind) {
        case TokenKind::MatchesKeyword:
            // pattern matching case statement
            matchesOrInside = consume();
            errored = parseCaseItems(
                caseKeyword.kind, itemBuffer, [](auto kind) { return isPossiblePattern(kind); },
                [this] {
                    auto& pattern = parsePattern();
                    Token tripleAnd;
                    ExpressionSyntax* patternExpr = nullptr;

                    if (peek(TokenKind::TripleAnd)) {
                        tripleAnd = consume();
                        patternExpr = &parseExpression();
                    }

                    auto colon = expect(TokenKind::Colon);
                    return &factory.patternCaseItem(pattern, tripleAnd, patternExpr, colon,
                                                    parseStatement());
                });
            break;
        case TokenKind::InsideKeyword:
            // range checking case statement
            matchesOrInside = consume();
            errored = parseCaseItems(
                caseKeyword.kind, itemBuffer,
                [](auto kind) { return isPossibleOpenRangeElement(kind); },
                [this] {
                    Token colon;
                    SmallVectorSized<TokenOrSyntax, 8> buffer;

                    parseList<isPossibleOpenRangeElement, isEndOfCaseItem>(
                        buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                        diag::ExpectedOpenRangeElement,
                        [this] { return &parseOpenRangeElement(); });
                    return &factory.standardCaseItem(buffer.copy(alloc), colon, parseStatement());
                });
            break;
        default:
            // normal case statement
            errored = parseCaseItems(
                caseKeyword.kind, itemBuffer, [](auto kind) { return isPossibleExpression(kind); },
                [this] {
                    Token colon;
                    SmallVectorSized<TokenOrSyntax, 8> buffer;

                    parseList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                        buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                        diag::ExpectedExpression, [this] { return &parseExpression(); });
                    return &factory.standardCaseItem(buffer.copy(alloc), colon, parseStatement());
                });
            break;
    }

    if (itemBuffer.empty() && !errored) {
        addDiag(diag::CaseStatementEmpty, caseKeyword.location())
            << LexerFacts::getTokenKindText(caseKeyword.kind);
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return factory.caseStatement(label, attributes, uniqueOrPriority, caseKeyword, openParen,
                                 caseExpr, closeParen, matchesOrInside, itemBuffer.copy(alloc),
                                 endcase);
}

DefaultCaseItemSyntax& Parser::parseDefaultCaseItem() {
    auto defaultKeyword = consume();

    Token colon;
    if (peek(TokenKind::Colon))
        colon = consume();

    return factory.defaultCaseItem(defaultKeyword, colon, parseStatement());
}

LoopStatementSyntax& Parser::parseLoopStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& statement = parseStatement();
    return factory.loopStatement(label, attributes, keyword, openParen, expr, closeParen,
                                 statement);
}

DoWhileStatementSyntax& Parser::parseDoWhileStatement(NamedLabelSyntax* label,
                                                      AttrList attributes) {
    auto doKeyword = consume();
    auto& statement = parseStatement();
    auto whileKeyword = expect(TokenKind::WhileKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto semi = expect(TokenKind::Semicolon);
    return factory.doWhileStatement(label, attributes, doKeyword, statement, whileKeyword,
                                    openParen, expr, closeParen, semi);
}

SyntaxNode& Parser::parseForInitializer() {
    if (isVariableDeclaration()) {
        auto varKeyword = consumeIf(TokenKind::VarKeyword);
        auto& type = parseDataType();

        // TODO: require initializer
        return factory.forVariableDeclaration(varKeyword, &type, parseDeclarator());
    }

    return factory.forVariableDeclaration(Token(), nullptr, parseDeclarator());
}

ForLoopStatementSyntax& Parser::parseForLoopStatement(NamedLabelSyntax* label,
                                                      AttrList attributes) {
    auto forKeyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token semi1;
    SmallVectorSized<TokenOrSyntax, 4> initializers;

    if (isVariableDeclaration()) {
        parseList<isPossibleForInitializer, isEndOfParenList>(
            initializers, TokenKind::Semicolon, TokenKind::Comma, semi1, RequireItems::False,
            diag::ExpectedForInitializer, [this] { return &parseForInitializer(); });
    }
    else {
        // TODO: require variable assignment
        parseList<isPossibleExpressionOrComma, isEndOfParenList>(
            initializers, TokenKind::Semicolon, TokenKind::Comma, semi1, RequireItems::False,
            diag::ExpectedForInitializer, [this] { return &parseExpression(); });
    }

    auto& stopExpr = parseExpression();
    auto semi2 = expect(TokenKind::Semicolon);

    Token closeParen;
    SmallVectorSized<TokenOrSyntax, 4> steps;
    parseList<isPossibleExpressionOrComma, isEndOfParenList>(
        steps, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
        diag::ExpectedExpression, [this] { return &parseExpression(); });

    return factory.forLoopStatement(label, attributes, forKeyword, openParen,
                                    initializers.copy(alloc), semi1, stopExpr, semi2,
                                    steps.copy(alloc), closeParen, parseStatement());
}

NameSyntax& Parser::parseForeachLoopVariable() {
    if (peek(TokenKind::Comma) || peek(TokenKind::CloseBracket))
        return factory.emptyIdentifierName(placeholderToken());

    auto identifier = expect(TokenKind::Identifier);
    return factory.identifierName(identifier);
}

ForeachLoopListSyntax& Parser::parseForeachLoopVariables() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& arrayName = parseName(NameOptions::ForeachName);

    span<TokenOrSyntax> list;
    Token openBracket;
    Token closeBracket;
    parseList<isIdentifierOrComma, isEndOfBracketedList>(
        TokenKind::OpenBracket, TokenKind::CloseBracket, TokenKind::Comma, openBracket, list,
        closeBracket, RequireItems::False, diag::ExpectedIdentifier,
        [this] { return &parseForeachLoopVariable(); }, AllowEmpty::True);

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return factory.foreachLoopList(openParen, arrayName, openBracket, list, closeBracket,
                                   closeParen);
}

ForeachLoopStatementSyntax& Parser::parseForeachLoopStatement(NamedLabelSyntax* label,
                                                              AttrList attributes) {

    auto keyword = consume();
    auto& vars = parseForeachLoopVariables();
    return factory.foreachLoopStatement(label, attributes, keyword, vars, parseStatement(false));
}

ReturnStatementSyntax& Parser::parseReturnStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto keyword = consume();

    ExpressionSyntax* expr = nullptr;
    if (!peek(TokenKind::Semicolon))
        expr = &parseExpression();

    auto semi = expect(TokenKind::Semicolon);
    return factory.returnStatement(label, attributes, keyword, expr, semi);
}

JumpStatementSyntax& Parser::parseJumpStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto keyword = consume();
    auto semi = expect(TokenKind::Semicolon);
    return factory.jumpStatement(label, attributes, keyword, semi);
}

ProceduralAssignStatementSyntax& Parser::parseProceduralAssignStatement(NamedLabelSyntax* label,
                                                                        AttrList attributes,
                                                                        SyntaxKind kind) {

    auto keyword = consume();
    auto& lvalue = parsePrimaryExpression(/* disallowVector */ false);
    auto equals = expect(TokenKind::Equals);
    auto& expr = parseExpression();
    auto semi = expect(TokenKind::Semicolon);
    return factory.proceduralAssignStatement(kind, label, attributes, keyword, lvalue, equals, expr,
                                             semi);
}

ProceduralDeassignStatementSyntax& Parser::parseProceduralDeassignStatement(NamedLabelSyntax* label,
                                                                            AttrList attributes,
                                                                            SyntaxKind kind) {

    auto keyword = consume();
    auto& variable = parsePrimaryExpression(/* disallowVector */ false);
    auto semi = expect(TokenKind::Semicolon);
    return factory.proceduralDeassignStatement(kind, label, attributes, keyword, variable, semi);
}

StatementSyntax& Parser::parseDisableStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto disable = consume();
    if (peek(TokenKind::ForkKeyword)) {
        auto fork = consume();
        return factory.disableForkStatement(label, attributes, disable, fork,
                                            expect(TokenKind::Semicolon));
    }

    auto& name = parseName();
    return factory.disableStatement(label, attributes, disable, name, expect(TokenKind::Semicolon));
}

StatementSyntax& Parser::parseAssertionStatement(NamedLabelSyntax* label, AttrList attributes) {
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
            THROW_UNREACHABLE;
    }

    Token keyword = consume();
    DeferredAssertionSyntax* deferred = nullptr;
    if (peek(TokenKind::Hash)) {
        auto hash = consume();
        auto zero = expect(TokenKind::IntegerLiteral);
        if (!zero.isMissing() && zero.intValue() != 0)
            addDiag(diag::DeferredDelayMustBeZero, zero.location());
        deferred = &factory.deferredAssertion(hash, zero, Token());
    }
    else if (peek(TokenKind::FinalKeyword)) {
        deferred = &factory.deferredAssertion(Token(), Token(), consume());
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto& parenExpr =
        factory.parenthesizedExpression(openParen, expr, expect(TokenKind::CloseParenthesis));
    auto& actionBlock = parseActionBlock();
    return factory.immediateAssertionStatement(assertionKind, label, attributes, keyword, deferred,
                                               parenExpr, actionBlock);
}

ConcurrentAssertionStatementSyntax& Parser::parseConcurrentAssertion(NamedLabelSyntax* label,
                                                                     AttrList attributes) {

    SyntaxKind kind = SyntaxKind::Unknown;
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
        default:
            THROW_UNREACHABLE;
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& spec = parsePropertySpec();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& action = parseActionBlock();

    return factory.concurrentAssertionStatement(
        kind, label, attributes, keyword, propertyOrSequence, openParen, spec, closeParen, action);
}

PropertySpecSyntax& Parser::parsePropertySpec() {
    TimingControlSyntax* timing = nullptr;
    if (peek(TokenKind::At))
        timing = parseTimingControl(/* isSequenceExpr */ true);

    DisableIffSyntax* disable = nullptr;
    if (peek(TokenKind::DisableKeyword)) {
        auto keyword = consume();
        auto iff = expect(TokenKind::IffKeyword);
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpressionOrDist();
        disable =
            &factory.disableIff(keyword, iff, openParen, expr, expect(TokenKind::CloseParenthesis));
    }
    // TODO: Parse all property expressions
    return factory.propertySpec(timing, disable, parseExpression());
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

    return factory.actionBlock(statement, elseClause);
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

        return &factory.namedBlockClause(colon, name);
    }
    return nullptr;
}

span<SyntaxNode*> Parser::parseBlockItems(TokenKind endKind, Token& end) {
    SmallVectorSized<SyntaxNode*, 16> buffer;
    auto kind = peek().kind;
    bool errored = false;
    bool sawStatement = false;
    bool erroredAboutDecls = false;

    while (!isEndKeyword(kind) && kind != TokenKind::EndOfFile) {
        SourceLocation loc = peek().location();
        SyntaxNode* newNode = nullptr;
        bool isStmt = false;

        if (isPortDeclaration()) {
            newNode = &parsePortDeclaration(parseAttributes());
        }
        else if (isVariableDeclaration()) {
            newNode = &parseVariableDeclaration(parseAttributes());
        }
        else if (isPossibleStatement(kind)) {
            newNode = &parseStatement();
            if (newNode->kind == SyntaxKind::EmptyStatement &&
                newNode->as<EmptyStatementSyntax>().semicolon.isMissing() &&
                loc == peek().location()) {
                skipToken(std::nullopt);
            }
            isStmt = true;
            sawStatement = true;
        }
        else {
            skipToken(errored ? std::nullopt : std::make_optional(diag::ExpectedStatement));
            errored = true;
        }

        if (newNode) {
            buffer.append(newNode);
            errored = false;

            if (!erroredAboutDecls && !isStmt && sawStatement) {
                addDiag(diag::DeclarationsAtStart, loc);
                erroredAboutDecls = true;
            }
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

    return buffer.copy(alloc);
}

BlockStatementSyntax& Parser::parseBlock(SyntaxKind blockKind, TokenKind endKind,
                                         NamedLabelSyntax* label, AttrList attributes) {
    auto begin = consume();
    auto name = parseNamedBlockClause();

    Token end;
    auto items = parseBlockItems(endKind, end);
    auto endName = parseNamedBlockClause();

    checkBlockNames(name, endName, label);
    return factory.blockStatement(blockKind, label, attributes, begin, name, items, end, endName);
}

StatementSyntax& Parser::parseWaitStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto wait = consume();
    if (peek(TokenKind::ForkKeyword)) {
        auto fork = consume();
        return factory.waitForkStatement(label, attributes, wait, fork,
                                         expect(TokenKind::Semicolon));
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    return factory.waitStatement(label, attributes, wait, openParen, expr, closeParen,
                                 parseStatement());
}

WaitOrderStatementSyntax& Parser::parseWaitOrderStatement(NamedLabelSyntax* label,
                                                          AttrList attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    SmallVectorSized<TokenOrSyntax, 4> buffer;

    Token closeParen;
    parseList<isIdentifierOrComma, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::True,
        diag::ExpectedIdentifier, [this] { return &parseName(); });

    return factory.waitOrderStatement(label, attributes, keyword, openParen, buffer.copy(alloc),
                                      closeParen, parseActionBlock());
}

RandCaseStatementSyntax& Parser::parseRandCaseStatement(NamedLabelSyntax* label,
                                                        AttrList attributes) {
    auto randCase = consume();
    SmallVectorSized<RandCaseItemSyntax*, 16> itemBuffer;

    while (isPossibleExpression(peek().kind)) {
        auto& expr = parseExpression();
        auto colon = expect(TokenKind::Colon);
        const auto loc = peek().location();
        auto& stmt = parseStatement();
        if (stmt.kind == SyntaxKind::EmptyStatement &&
            stmt.as<EmptyStatementSyntax>().semicolon.isMissing() && loc == peek().location()) {
            skipToken(std::nullopt);
        }
        itemBuffer.append(&factory.randCaseItem(expr, colon, stmt));
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return factory.randCaseStatement(label, attributes, randCase, itemBuffer.copy(alloc), endcase);
}

EventTriggerStatementSyntax& Parser::parseEventTriggerStatement(NamedLabelSyntax* label,
                                                                AttrList attributes) {
    auto trigger = consume();

    SyntaxKind kind = SyntaxKind::BlockingEventTriggerStatement;
    TimingControlSyntax* timing = nullptr;
    if (trigger.kind == TokenKind::MinusDoubleArrow) {
        kind = SyntaxKind::NonblockingEventTriggerStatement;
        timing = parseTimingControl(/* isSequenceExpr */ false);
    }

    return factory.eventTriggerStatement(kind, label, attributes, trigger, timing, parseName());
}

StatementSyntax& Parser::parseVoidCallStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto keyword = consume();
    auto apostrophe = expect(TokenKind::Apostrophe);
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto semi = expect(TokenKind::Semicolon);
    return factory.voidCastedCallStatement(label, attributes, keyword, apostrophe, openParen, expr,
                                           closeParen, semi);
}

} // namespace slang
