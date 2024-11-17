//------------------------------------------------------------------------------
// Parser_statements.cpp
// Statement-related parsing methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/parsing/Parser.h"

namespace slang::parsing {

using namespace syntax;

StatementSyntax& Parser::parseStatement(bool allowEmpty, bool allowSuperNew) {
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
            auto& body = parseStatement();
            checkEmptyBody(body, forever, "forever loop"sv);
            return factory.foreverStatement(label, attributes, forever, body);
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
            auto timingControl = parseTimingControl();
            SLANG_ASSERT(timingControl);
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
        case TokenKind::RandSequenceKeyword:
            return parseRandSequenceStatement(label, attributes);
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
        case TokenKind::Identifier: {
            // This could be a checker instantiation.
            uint32_t index = 1;
            if (peek(index).kind == TokenKind::DoubleColon &&
                peek(index + 1).kind == TokenKind::Identifier) {
                index = 3;
            }

            if (peek(index).kind == TokenKind::Identifier &&
                peek(index + 1).kind == TokenKind::OpenParenthesis) {
                return parseCheckerStatement(label, attributes);
            }

            break;
        }
        case TokenKind::UnitSystemName:
            if (peek(1).kind == TokenKind::DoubleColon && peek(2).kind == TokenKind::Identifier &&
                peek(3).kind == TokenKind::Identifier &&
                peek(4).kind == TokenKind::OpenParenthesis) {
                return parseCheckerStatement(label, attributes);
            }
            break;
        default:
            break;
    }

    // everything else should be some kind of expression
    if (isPossibleExpression(peek().kind)) {
        bitmask<ExpressionOptions> options = ExpressionOptions::ProceduralAssignmentContext;
        if (allowSuperNew)
            options |= ExpressionOptions::AllowSuperNewCall;

        auto& expr = parseSubExpression(options, 0);
        return factory.expressionStatement(label, attributes, expr, expect(TokenKind::Semicolon));
    }

    addDiag(diag::ExpectedStatement, peek().location());
    return factory.emptyStatement(label, attributes,
                                  missingToken(TokenKind::Semicolon, peek().location()));
}

ElseClauseSyntax* Parser::parseElseClause() {
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        auto& stmt = parseStatement();
        if (stmt.kind == SyntaxKind::ConditionalStatement) {
            if (auto tok = stmt.as<ConditionalStatementSyntax>().uniqueOrPriority)
                addDiag(diag::UniquePriorityAfterElse, tok.range());
        }
        return &factory.elseClause(elseKeyword, stmt);
    }
    return nullptr;
}

ConditionalStatementSyntax& Parser::parseConditionalStatement(NamedLabelSyntax* label,
                                                              AttrList attributes,
                                                              Token uniqueOrPriority) {
    auto ifKeyword = expect(TokenKind::IfKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token closeParen;
    auto& predicate = parseConditionalPredicate(parseExpression(), TokenKind::CloseParenthesis,
                                                closeParen);
    auto& statement = parseStatement();
    auto elseClause = parseElseClause();

    if (elseClause)
        checkEmptyBody(*elseClause->clause, elseClause->elseKeyword, "else clause"sv);
    else
        checkEmptyBody(statement, closeParen, "if statement"sv);

    return factory.conditionalStatement(label, attributes, uniqueOrPriority, ifKeyword, openParen,
                                        predicate, closeParen, statement, elseClause);
}

template<typename IsItemFunc, typename ParseItemFunc>
bool Parser::parseCaseItems(TokenKind caseKind, SmallVectorBase<CaseItemSyntax*>& itemBuffer,
                            IsItemFunc&& isItem, ParseItemFunc&& parseItem) {
    SourceLocation lastDefault;
    bool errored = false;

    while (true) {
        auto current = peek();
        auto kind = current.kind;
        if (kind == TokenKind::DefaultKeyword) {
            if (lastDefault && !errored) {
                auto& diag = addDiag(diag::MultipleDefaultCases, peek().location());
                diag << LexerFacts::getTokenKindText(caseKind);
                diag.addNote(diag::NotePreviousDefinition, lastDefault);
                errored = true;
            }

            lastDefault = peek().location();
            itemBuffer.push_back(&parseDefaultCaseItem());
        }
        else if (isItem(kind)) {
            itemBuffer.push_back(parseItem());
            if (current == peek()) {
                // parseItem() didn't consume any tokens, so we'll be stuck
                // in an infinite loop if we don't skip a token here.
                skipToken(std::nullopt);
            }
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
    SmallVector<CaseItemSyntax*> itemBuffer;
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
                [](auto kind) { return isPossibleValueRangeElement(kind); },
                [this] {
                    Token colon;
                    SmallVector<TokenOrSyntax, 8> buffer;

                    parseList<isPossibleValueRangeElement, isEndOfCaseItem>(
                        buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                        diag::ExpectedValueRangeElement,
                        [this] { return &parseValueRangeElement(); });
                    return &factory.standardCaseItem(buffer.copy(alloc), colon, parseStatement());
                });
            break;
        default:
            // normal case statement
            errored = parseCaseItems(
                caseKeyword.kind, itemBuffer, [](auto kind) { return isPossibleExpression(kind); },
                [this] {
                    Token colon;
                    SmallVector<TokenOrSyntax, 8> buffer;

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
    checkEmptyBody(statement, closeParen,
                   keyword.kind == TokenKind::WhileKeyword ? "while loop"sv : "repeat loop"sv);
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
        auto& decl = parseDeclarator(/* allowMinTypMax */ false,
                                     /* requireInitializers */ true);
        auto& result = factory.forVariableDeclaration(varKeyword, &type, decl);
        result.previewNode = std::exchange(previewNode, nullptr);
        return result;
    }

    return factory.forVariableDeclaration(Token(), nullptr, parseDeclarator());
}

ForLoopStatementSyntax& Parser::parseForLoopStatement(NamedLabelSyntax* label,
                                                      AttrList attributes) {
    auto forKeyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token semi1;
    SmallVector<TokenOrSyntax, 4> initializers;

    if (isVariableDeclaration()) {
        parseList<isPossibleForInitializer, isEndOfParenList>(
            initializers, TokenKind::Semicolon, TokenKind::Comma, semi1, RequireItems::False,
            diag::ExpectedForInitializer, [this] { return &parseForInitializer(); });
    }
    else {
        parseList<isPossibleExpressionOrComma, isEndOfParenList>(
            initializers, TokenKind::Semicolon, TokenKind::Comma, semi1, RequireItems::False,
            diag::ExpectedForInitializer, [this] {
                auto& expr = parseExpression();
                if (expr.kind != SyntaxKind::AssignmentExpression &&
                    (expr.kind != SyntaxKind::IdentifierName ||
                     !expr.getFirstToken().isMissing())) {
                    // Initializer expressions must be variable assignments.
                    addDiag(diag::InvalidForInitializer, expr.sourceRange());
                }
                return &expr;
            });
    }

    ExpressionSyntax* stopExpr = nullptr;
    Token semi2;
    if (peek(TokenKind::Semicolon)) {
        semi2 = consume();
    }
    else {
        stopExpr = &parseExpression();
        semi2 = expect(TokenKind::Semicolon);
    }

    Token closeParen;
    SmallVector<TokenOrSyntax, 4> steps;
    parseList<isPossibleExpressionOrComma, isEndOfParenList>(
        steps, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
        diag::ExpectedExpression, [this] { return &parseExpression(); });

    auto& body = parseStatement();

    checkEmptyBody(body, closeParen, "for loop"sv);

    return factory.forLoopStatement(label, attributes, forKeyword, openParen,
                                    initializers.copy(alloc), semi1, stopExpr, semi2,
                                    steps.copy(alloc), closeParen, body);
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

    if (arrayName.kind == SyntaxKind::IdentifierSelectName)
        addDiag(diag::NonstandardForeach, arrayName.sourceRange());

    std::span<TokenOrSyntax> list;
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
    auto& expr = parseExpression();
    if (expr.kind != SyntaxKind::AssignmentExpression)
        addDiag(diag::ExpectedContinuousAssignment, expr.sourceRange());

    auto semi = expect(TokenKind::Semicolon);
    return factory.proceduralAssignStatement(kind, label, attributes, keyword, expr, semi);
}

ProceduralDeassignStatementSyntax& Parser::parseProceduralDeassignStatement(NamedLabelSyntax* label,
                                                                            AttrList attributes,
                                                                            SyntaxKind kind) {
    auto keyword = consume();
    auto& variable = parsePrimaryExpression(ExpressionOptions::None);
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
            SLANG_UNREACHABLE;
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
    auto& parenExpr = factory.parenthesizedExpression(openParen, expr,
                                                      expect(TokenKind::CloseParenthesis));
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
            SLANG_UNREACHABLE;
    }

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& spec = parsePropertySpec();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& action = parseActionBlock();

    return factory.concurrentAssertionStatement(kind, label, attributes, keyword,
                                                propertyOrSequence, openParen, spec, closeParen,
                                                action);
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
        disable = &factory.disableIff(keyword, iff, openParen, expr,
                                      expect(TokenKind::CloseParenthesis));
    }

    return factory.propertySpec(timing, disable, parsePropertyExpr(0));
}

ActionBlockSyntax& Parser::parseActionBlock() {
    StatementSyntax* statement = nullptr;
    ElseClauseSyntax* elseClause = nullptr;

    if (peek(TokenKind::ElseKeyword))
        elseClause = parseElseClause();
    else {
        statement = &parseStatement();
        if (statement->kind != SyntaxKind::EmptyStatement)
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

std::span<SyntaxNode*> Parser::parseBlockItems(TokenKind endKind, Token& end, bool inConstructor) {
    SmallVector<SyntaxNode*, 16> buffer;
    auto kind = peek().kind;
    bool errored = false;
    bool sawStatement = false;
    bool erroredAboutDecls = false;

    while (!isEndKeyword(kind) && kind != endKind && kind != TokenKind::EndOfFile) {
        SourceLocation loc = peek().location();
        SyntaxNode* newNode = nullptr;
        bool isStmt = false;

        if (isPortDeclaration(/* inStatement */ true)) {
            newNode = &parsePortDeclaration(parseAttributes());
        }
        else if (isVariableDeclaration()) {
            newNode = &parseVariableDeclaration(parseAttributes());
        }
        else if (isPossibleStatement(kind)) {
            newNode = &parseStatement(/* allowEmpty */ true,
                                      /* allowSuperNew */ inConstructor && !sawStatement);
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
            newNode->previewNode = std::exchange(previewNode, nullptr);
            buffer.push_back(newNode);
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
    auto items = parseBlockItems(endKind, end, /* inConstructor */ false);
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
    SmallVector<TokenOrSyntax, 4> buffer;

    Token closeParen;
    parseList<isIdentifierOrComma, isEndOfParenList>(buffer, TokenKind::CloseParenthesis,
                                                     TokenKind::Comma, closeParen,
                                                     RequireItems::True, diag::ExpectedIdentifier,
                                                     [this] { return &parseName(); });

    return factory.waitOrderStatement(label, attributes, keyword, openParen, buffer.copy(alloc),
                                      closeParen, parseActionBlock());
}

RandCaseStatementSyntax& Parser::parseRandCaseStatement(NamedLabelSyntax* label,
                                                        AttrList attributes) {
    auto randCase = consume();
    SmallVector<RandCaseItemSyntax*> itemBuffer;

    while (isPossibleExpression(peek().kind)) {
        auto curr = peek();
        auto& expr = parseExpression();
        auto colon = expect(TokenKind::Colon);
        auto& stmt = parseStatement();

        // If there are no consumed tokens then expression and statement were not parsed.
        if (curr == peek())
            skipToken(std::nullopt);
        else
            itemBuffer.push_back(&factory.randCaseItem(expr, colon, stmt));
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
        timing = parseTimingControl();
    }

    auto& name = parseName();
    return factory.eventTriggerStatement(kind, label, attributes, trigger, timing, name,
                                         expect(TokenKind::Semicolon));
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

RsProdItemSyntax& Parser::parseRsProdItem() {
    auto name = expect(TokenKind::Identifier);

    ArgumentListSyntax* args = nullptr;
    if (peek(TokenKind::OpenParenthesis))
        args = &parseArgumentList();

    return factory.rsProdItem(name, args);
}

RsCodeBlockSyntax& Parser::parseRsCodeBlock() {
    auto openBrace = expect(TokenKind::OpenBrace);

    Token closeBrace;
    auto items = parseBlockItems(TokenKind::CloseBrace, closeBrace, /* inConstructor */ false);

    return factory.rsCodeBlock(openBrace, items, closeBrace);
}

RsCaseSyntax& Parser::parseRsCase() {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    SmallVector<RsCaseItemSyntax*> itemBuffer;
    SourceLocation lastDefault;
    bool errored = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::DefaultKeyword) {
            if (lastDefault && !errored) {
                auto& diag = addDiag(diag::MultipleDefaultCases, peek().location()) << "case"sv;
                diag.addNote(diag::NotePreviousDefinition, lastDefault);
                errored = true;
            }

            lastDefault = peek().location();

            auto def = consume();
            auto colon = consumeIf(TokenKind::Colon);
            auto& item = parseRsProdItem();
            auto semi = expect(TokenKind::Semicolon);
            itemBuffer.push_back(&factory.defaultRsCaseItem(def, colon, item, semi));
        }
        else if (isPossibleExpression(kind)) {
            Token colon;
            SmallVector<TokenOrSyntax, 8> buffer;
            parseList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });

            auto& item = parseRsProdItem();
            auto semi = expect(TokenKind::Semicolon);
            itemBuffer.push_back(
                &factory.standardRsCaseItem(buffer.copy(alloc), colon, item, semi));
        }
        else {
            break;
        }
    }

    if (itemBuffer.empty())
        addDiag(diag::CaseStatementEmpty, keyword.location()) << "case"sv;

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return factory.rsCase(keyword, openParen, condition, closeParen, itemBuffer.copy(alloc),
                          endcase);
}

RsProdSyntax* Parser::parseRsProd() {
    switch (peek().kind) {
        case TokenKind::Identifier:
            return &parseRsProdItem();
        case TokenKind::IfKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& ifItem = parseRsProdItem();

            RsElseClauseSyntax* elseClause = nullptr;
            if (peek(TokenKind::ElseKeyword)) {
                auto elseKeyword = consume();
                auto& elseItem = parseRsProdItem();
                elseClause = &factory.rsElseClause(elseKeyword, elseItem);
            }

            return &factory.rsIfElse(keyword, openParen, condition, closeParen, ifItem, elseClause);
        }
        case TokenKind::RepeatKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& item = parseRsProdItem();

            return &factory.rsRepeat(keyword, openParen, expr, closeParen, item);
        }
        case TokenKind::CaseKeyword:
            return &parseRsCase();
        case TokenKind::OpenBrace:
            return &parseRsCodeBlock();
        default:
            return nullptr;
    }
}

RsRuleSyntax& Parser::parseRsRule() {
    RandJoinClauseSyntax* randJoin = nullptr;
    if (peek(TokenKind::RandKeyword)) {
        auto rand = consume();
        auto join = expect(TokenKind::JoinKeyword);

        ParenthesizedExpressionSyntax* parenExpr = nullptr;
        if (peek(TokenKind::OpenParenthesis)) {
            auto openParen = consume();
            auto& expr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            parenExpr = &factory.parenthesizedExpression(openParen, expr, closeParen);
        }

        randJoin = &factory.randJoinClause(rand, join, parenExpr);
    }

    SmallVector<RsProdSyntax*> prods;
    while (true) {
        auto prod = parseRsProd();
        if (!prod)
            break;

        prods.push_back(prod);
        if (randJoin && prod->kind != SyntaxKind::RsProdItem)
            addDiag(diag::RandJoinProdItem, prod->sourceRange());
    }

    if (randJoin && prods.size() < 2) {
        SourceRange range = randJoin->sourceRange();
        if (!prods.empty())
            range = SourceRange{range.start(), prods.back()->getLastToken().range().end()};

        addDiag(diag::RandJoinNotEnough, range);
    }

    RsWeightClauseSyntax* weightClause = nullptr;
    if (peek(TokenKind::ColonEquals)) {
        auto colonEqual = consume();
        auto& weight = parsePrimaryExpression(ExpressionOptions::DisallowVectors);

        RsCodeBlockSyntax* codeBlock = nullptr;
        if (peek(TokenKind::OpenBrace))
            codeBlock = &parseRsCodeBlock();

        weightClause = &factory.rsWeightClause(colonEqual, weight, codeBlock);
    }

    return factory.rsRule(randJoin, prods.copy(alloc), weightClause);
}

ProductionSyntax& Parser::parseProduction() {
    // Data type is optional so we have to scan ahead to disambiguate the production name.
    DataTypeSyntax* dataType = nullptr;
    if (!peek(TokenKind::Identifier))
        dataType = &parseDataType(TypeOptions::AllowVoid);
    else {
        auto next = peek(1);
        if (next.kind != TokenKind::OpenParenthesis && next.kind != TokenKind::Colon)
            dataType = &parseDataType(TypeOptions::AllowVoid);
    }

    auto name = expect(TokenKind::Identifier);
    auto ports = parseFunctionPortList({});
    auto colon = expect(TokenKind::Colon);

    Token semi;
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleRsRule, isSemicolon>(buffer, TokenKind::Semicolon, TokenKind::Or, semi,
                                             RequireItems::True, diag::ExpectedRsRule,
                                             [this] { return &parseRsRule(); });

    return factory.production(dataType, name, ports, colon, buffer.copy(alloc), semi);
}

StatementSyntax& Parser::parseRandSequenceStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto firstProd = consumeIf(TokenKind::Identifier);
    auto closeParen = expect(TokenKind::CloseParenthesis);

    SmallVector<ProductionSyntax*> productions;
    while (isPossibleDataType(peek().kind)) {
        auto curr = peek();
        productions.push_back(&parseProduction());
        productions.back()->previewNode = std::exchange(previewNode, nullptr);

        // If there are no consumed tokens then production was not parsed.
        if (curr == peek())
            skipToken(std::nullopt);
    }

    if (productions.empty())
        addDiag(diag::ExpectedRsRule, peek().location());

    auto endsequence = expect(TokenKind::EndSequenceKeyword);
    return factory.randSequenceStatement(label, attributes, keyword, openParen, firstProd,
                                         closeParen, productions.copy(alloc), endsequence);
}

StatementSyntax& Parser::parseCheckerStatement(NamedLabelSyntax* label, AttrList attributes) {
    auto& instance = parseCheckerInstantiation({});
    return factory.checkerInstanceStatement(label, attributes, instance);
}

void Parser::checkEmptyBody(const SyntaxNode& syntax, Token prevToken,
                            std::string_view syntaxName) {
    if (syntax.kind != SyntaxKind::EmptyStatement || prevToken.isMissing())
        return;

    auto& ess = syntax.as<EmptyStatementSyntax>();
    if (ess.label || !ess.attributes.empty() || ess.semicolon.isMissing() ||
        !ess.semicolon.isOnSameLine()) {
        return;
    }

    addDiag(diag::EmptyBody, ess.semicolon.location()) << syntaxName;
}

} // namespace slang::parsing
