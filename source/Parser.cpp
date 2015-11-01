#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "StringRef.h"
#include "SourceTracker.h"
#include "Token.h"
#include "Diagnostics.h"
#include "Lexer.h"
#include "Preprocessor.h"
#include "Parser.h"

namespace {

using namespace slang;

bool isPossibleArgument(TokenKind kind);
bool isComma(TokenKind kind);
bool isSemicolon(TokenKind kind);
bool isIdentifierOrComma(TokenKind kind);
bool isPossibleExpressionOrComma(TokenKind kind);
bool isPossibleExpressionOrTripleAnd(TokenKind kind);
bool isPossibleInsideElement(TokenKind kind);
bool isPossiblePattern(TokenKind kind);
bool isPossibleDelayOrEventControl(TokenKind kind);
bool isEndKeyword(TokenKind kind);
bool isDeclarationModifier(TokenKind kind);
bool isEndOfParenList(TokenKind kind);
bool isEndOfBracedList(TokenKind kind);
bool isEndOfCaseItem(TokenKind kind);
bool isEndOfConditionalPredicate(TokenKind kind);
bool isEndOfAttribute(TokenKind kind);
bool isNotInType(TokenKind kind);

}

namespace slang {

Parser::Parser(Lexer& lexer) :
    lexer(lexer),
    alloc(lexer.getPreprocessor().getAllocator()),
    diagnostics(lexer.getPreprocessor().getDiagnostics()),
    window(lexer) {
}

StatementSyntax* Parser::parseStatement() {
    StatementLabelSyntax* label = nullptr;
    if (peek()->kind == TokenKind::Identifier && peek(1)->kind == TokenKind::Colon) {
        auto name = consume();
        label = alloc.emplace<StatementLabelSyntax>(name, consume());
    }

    auto attributes = parseAttributes();

    switch (peek()->kind) {
        case TokenKind::UniqueKeyword:
        case TokenKind::Unique0Keyword:
        case TokenKind::PriorityKeyword: {
            auto modifier = consume();
            switch (peek()->kind) {
                case TokenKind::IfKeyword:
                    return parseConditionalStatement(label, attributes, modifier);
                case TokenKind::CaseKeyword:
                case TokenKind::CaseXKeyword:
                case TokenKind::CaseZKeyword:
                    return parseCaseStatement(label, attributes, modifier, consume());
                default:
                    // TODO: handle error case
                    break;
            }
            break;
        }
        case TokenKind::CaseKeyword:
        case TokenKind::CaseXKeyword:
        case TokenKind::CaseZKeyword:
            return parseCaseStatement(label, attributes, nullptr, consume());
        case TokenKind::IfKeyword:
            return parseConditionalStatement(label, attributes, nullptr);
        case TokenKind::ForeverKeyword: {
            auto forever = consume();
            return alloc.emplace<ForeverStatementSyntax>(label, attributes, forever, parseStatement());
        }
        case TokenKind::RepeatKeyword:
        case TokenKind::WhileKeyword:
            return parseLoopStatement(label, attributes);
        case TokenKind::DoKeyword:
            return parseDoWhileStatement(label, attributes);
        case TokenKind::ReturnKeyword:
            return parseReturnStatement(label, attributes);
        case TokenKind::BreakKeyword:
        case TokenKind::ContinueKeyword:
            return parseJumpStatement(label, attributes);
        case TokenKind::Hash:
        case TokenKind::DoubleHash:
        case TokenKind::At:
        case TokenKind::AtStar: {
            auto timingControl = parseTimingControl(/* allowRepeat */ false);
            return alloc.emplace<TimingControlStatementSyntax>(label, attributes, timingControl, parseStatement());
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
            return parseSequentialBlock(label, attributes);
        case TokenKind::Semicolon:
            // TODO: no label allowed on semicolon
            return alloc.emplace<EmptyStatementSyntax>(label, attributes, consume());
    }

    return nullptr;
}

ConditionalStatementSyntax* Parser::parseConditionalStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority) {
    auto ifKeyword = expect(TokenKind::IfKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token* closeParen;
    auto predicate = parseConditionalPredicate(parseExpression(), TokenKind::CloseParenthesis, closeParen);
    auto statement = parseStatement();

    ElseClauseSyntax* elseClause = nullptr;
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        elseClause = alloc.emplace<ElseClauseSyntax>(elseKeyword, parseStatement());
    }

    return alloc.emplace<ConditionalStatementSyntax>(
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

CaseStatementSyntax* Parser::parseCaseStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority, Token* caseKeyword) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto caseExpr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    Token* matchesOrInside = nullptr;
    auto itemBuffer = nodePool.getAs<CaseItemSyntax*>();

    switch (peek()->kind) {
        case TokenKind::MatchesKeyword:
            // pattern matching case statement
            matchesOrInside = consume();
            while (true) {
                auto kind = peek()->kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(parseDefaultCaseItem());
                else if (isPossiblePattern(kind)) {
                    auto pattern = parsePattern();
                    Token* tripleAnd = nullptr;
                    ExpressionSyntax* patternExpr = nullptr;

                    if (peek(TokenKind::TripleAnd)) {
                        tripleAnd = consume();
                        patternExpr = parseExpression();
                    }

                    auto colon = expect(TokenKind::Colon);
                    itemBuffer.append(alloc.emplace<PatternCaseItemSyntax>(pattern, tripleAnd, patternExpr, colon, parseStatement()));
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
                auto kind = peek()->kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(parseDefaultCaseItem());
                else if (isPossibleInsideElement(kind)) {
                    Token* colon;
                    auto buffer = tosPool.get();

                    parseSeparatedList<isPossibleInsideElement, isEndOfCaseItem>(
                        buffer,
                        TokenKind::Colon,
                        TokenKind::Comma,
                        colon,
                        &Parser::parseInsideElement
                    );

                    itemBuffer.append(alloc.emplace<StandardCaseItemSyntax>(buffer.copy(alloc), colon, parseStatement()));
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
                auto kind = peek()->kind;
                if (kind == TokenKind::DefaultKeyword)
                    itemBuffer.append(parseDefaultCaseItem());
                else if (isPossibleExpression(kind)) {
                    Token* colon;
                    auto buffer = tosPool.get();

                    parseSeparatedList<isPossibleInsideElement, isEndOfCaseItem>(
                        buffer,
                        TokenKind::Colon,
                        TokenKind::Comma,
                        colon,
                        &Parser::parseExpression
                    );

                    itemBuffer.append(alloc.emplace<StandardCaseItemSyntax>(buffer.copy(alloc), colon, parseStatement()));
                }
                else {
                    // no idea what this is; break out and clean up
                    break;
                }
            }
            break;
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return alloc.emplace<CaseStatementSyntax>(
        label,
        attributes,
        uniqueOrPriority,
        caseKeyword,
        openParen,
        caseExpr,
        closeParen,
        matchesOrInside,
        itemBuffer.copy(alloc),
        endcase
    );
}

DefaultCaseItemSyntax* Parser::parseDefaultCaseItem() {
    auto defaultKeyword = consume();

    Token* colon = nullptr;
    if (peek(TokenKind::Colon))
        colon = consume();

    return alloc.emplace<DefaultCaseItemSyntax>(defaultKeyword, colon, parseStatement());
}

LoopStatementSyntax* Parser::parseLoopStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto statement = parseStatement();
    return alloc.emplace<LoopStatementSyntax>(label, attributes, keyword, openParen, expr, closeParen, statement);
}

DoWhileStatementSyntax* Parser::parseDoWhileStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto doKeyword = consume();
    auto statement = parseStatement();
    auto whileKeyword = expect(TokenKind::WhileKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto expr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<DoWhileStatementSyntax>(label, attributes, doKeyword, statement, whileKeyword, openParen, expr, closeParen, semi);
}

ReturnStatementSyntax* Parser::parseReturnStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    ExpressionSyntax* expr = nullptr;
    if (!peek(TokenKind::Semicolon))
        expr = parseExpression();

    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<ReturnStatementSyntax>(label, attributes, keyword, expr, semi);
}

JumpStatementSyntax* Parser::parseJumpStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<JumpStatementSyntax>(label, attributes, keyword, semi);
}

AssignmentStatementSyntax* Parser::parseAssignmentStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    ExpressionSyntax* lvalue = parsePrimaryExpression();

    // non-blocking assignments
    auto kind = peek()->kind;
    if (kind == TokenKind::LessThanEquals) {
        auto op = consume();
        auto timingControl = parseTimingControl(/* allowRepeat */ true);
        auto expr = parseExpression();
        return alloc.emplace<AssignmentStatementSyntax>(
            SyntaxKind::NonblockingAssignmentStatement,
            label,
            attributes,
            lvalue,
            op,
            timingControl,
            expr,
            expect(TokenKind::Semicolon)
        );
    }

    // special case blocking assignments
    if (kind == TokenKind::Equals) {
        auto op = consume();
        kind = peek()->kind;
        if (isPossibleDelayOrEventControl(kind)) {
            auto timingControl = parseTimingControl(/* allowRepeat */ true);
            auto expr = parseExpression();
            return alloc.emplace<AssignmentStatementSyntax>(
                SyntaxKind::BlockingAssignmentStatement,
                label,
                attributes,
                lvalue,
                op,
                timingControl,
                expr,
                expect(TokenKind::Semicolon)
            );
        }

        auto expr = parseAssignmentExpression();
        return alloc.emplace<AssignmentStatementSyntax>(
            SyntaxKind::BlockingAssignmentStatement,
            label,
            attributes,
            lvalue,
            op,
            nullptr,
            expr,
            expect(TokenKind::Semicolon)
        );
    }

    // TODO: handle error case where operator is missing
    auto op = consume();
    return alloc.emplace<AssignmentStatementSyntax>(
        getAssignmentStatement(kind),
        label,
        attributes,
        lvalue,
        op,
        nullptr,
        parseExpression(),
        expect(TokenKind::Semicolon)
    );
}

ProceduralAssignStatementSyntax* Parser::parseProceduralAssignStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind) {
    auto keyword = consume();
    auto lvalue = parsePrimaryExpression();
    auto equals = expect(TokenKind::Equals);
    auto expr = parseExpression();
    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<ProceduralAssignStatementSyntax>(kind, label, attributes, keyword, lvalue, equals, expr, semi);
}

ProceduralDeassignStatementSyntax* Parser::parseProceduralDeassignStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind) {
    auto keyword = consume();
    auto variable = parsePrimaryExpression();
    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<ProceduralDeassignStatementSyntax>(kind, label, attributes, keyword, variable, semi);
}

StatementSyntax* Parser::parseDisableStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto disable = consume();
    if (peek(TokenKind::ForkKeyword)) {
        auto fork = consume();
        return alloc.emplace<DisableForkStatementSyntax>(label, attributes, disable, fork, expect(TokenKind::Semicolon));
    }

    auto name = parseName();
    return alloc.emplace<DisableStatementSyntax>(label, attributes, disable, name, expect(TokenKind::Semicolon));
}

NamedBlockClauseSyntax* Parser::parseNamedBlockClause() {
    if (peek(TokenKind::Colon)) {
        auto colon = consume();
        return alloc.emplace<NamedBlockClauseSyntax>(colon, expect(TokenKind::Identifier));
    }
    return nullptr;
}

SequentialBlockStatementSyntax* Parser::parseSequentialBlock(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto begin = consume();
    auto name = parseNamedBlockClause();

    auto buffer = nodePool.getAs<StatementSyntax*>();
    auto kind = peek()->kind;
    while (!isEndKeyword(kind) && kind != TokenKind::EndOfFile) {
        if (isPossibleBlockDeclaration())
            buffer.append(parseBlockDeclaration());
        else if (isPossibleStatement(kind))
            buffer.append(parseStatement());
        else {
            // TODO: skipped tokens
        }
        kind = peek()->kind;
    }

    auto end = expect(TokenKind::EndKeyword);
    auto endName = parseNamedBlockClause();
    return alloc.emplace<SequentialBlockStatementSyntax>(label, attributes, begin, name, buffer.copy(alloc), end, endName);
}

ExpressionSyntax* Parser::parseExpression() {
    return parseSubExpression(0);
}

ExpressionSyntax* Parser::parseMinTypMaxExpression() {
    ExpressionSyntax* first = parseSubExpression(0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto typ = parseSubExpression(0);
    auto colon2 = expect(TokenKind::Colon);
    auto max = parseSubExpression(0);

    return alloc.emplace<MinTypMaxExpressionSyntax>(first, colon1, typ, colon2, max);
}

ExpressionSyntax* Parser::parseSubExpression(int precedence) {
    ExpressionSyntax* leftOperand = nullptr;
    int newPrecedence = 0;

    auto current = peek();
    if (current->kind == TokenKind::TaggedKeyword) {
        // TODO: check for trailing expression
        auto tagged = consume();
        auto member = expect(TokenKind::Identifier);
        return alloc.emplace<TaggedUnionExpressionSyntax>(tagged, member, nullptr);
    }

    SyntaxKind opKind = getUnaryPrefixExpression(current->kind);
    if (opKind != SyntaxKind::Unknown) {
        auto opToken = consume();
        auto attributes = parseAttributes();

        newPrecedence = getPrecedence(opKind);
        ExpressionSyntax* operand = parseSubExpression(newPrecedence);
        leftOperand = alloc.emplace<PrefixUnaryExpressionSyntax>(opKind, opToken, attributes, operand);
    }
    else {
        // not a unary operator, so must be a primary expression
        leftOperand = parsePrimaryExpression();
    }

    while (true) {
        // either a binary operator, or we're done
        current = peek();
        opKind = getBinaryExpression(current->kind);
        if (opKind == SyntaxKind::Unknown)
            break;

        // see if we should take this operator or if it's part of our parent due to precedence
        newPrecedence = getPrecedence(opKind);
        if (newPrecedence < precedence)
            break;

        // if we have a precedence tie, check associativity
        if (newPrecedence == precedence && !isRightAssociative(opKind))
            break;

        // take the operator
        if (opKind == SyntaxKind::InsideExpression)
            leftOperand = parseInsideExpression(leftOperand);
        else {
            auto opToken = consume();
            auto attributes = parseAttributes();
            auto rightOperand = parseSubExpression(newPrecedence);
            leftOperand = alloc.emplace<BinaryExpressionSyntax>(opKind, leftOperand, opToken, attributes, rightOperand);
        }
    }

    // if we see the matches keyword or &&& we're in a pattern conditional predicate
    // if we see a question mark, we were in a simple conditional predicate
    auto logicalOrPrecedence = getPrecedence(SyntaxKind::LogicalOrExpression);
    if (current->kind == TokenKind::MatchesKeyword || current->kind == TokenKind::TripleAnd ||
        (current->kind == TokenKind::Question && precedence < logicalOrPrecedence)) {

        Token* question;
        auto predicate = parseConditionalPredicate(leftOperand, TokenKind::Question, question);
        auto attributes = parseAttributes();
        auto left = parseSubExpression(logicalOrPrecedence - 1);
        auto colon = expect(TokenKind::Colon);
        auto right = parseSubExpression(logicalOrPrecedence - 1);
        leftOperand = alloc.emplace<ConditionalExpressionSyntax>(predicate, question, attributes, left, colon, right);
    }
    
    return leftOperand;
}

ExpressionSyntax* Parser::parsePrimaryExpression() {
    ExpressionSyntax* expr;
    TokenKind kind = peek()->kind;
    switch (kind) {
        case TokenKind::StringLiteral:
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
        case TokenKind::NullKeyword:
        case TokenKind::Dollar: {
            auto literal = consume();
            expr = alloc.emplace<LiteralExpressionSyntax>(getLiteralExpression(literal->kind), literal);
            break;
        }
        case TokenKind::SystemIdentifier: {
            auto identifier = consume();
            expr = alloc.emplace<KeywordNameSyntax>(SyntaxKind::SystemName, identifier);
            break;
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            expr = parseMinTypMaxExpression();

            auto closeParen = expect(TokenKind::CloseParenthesis);
            expr = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, expr, closeParen);
            break;
        }
        case TokenKind::OpenBrace: {
            // several different things this could be:
            // 1. empty queue expression { }
            // 2. streaming concatenation {>> {expr}}
            // 3. multiple concatenation {expr {concat}}
            // 4. concatenation {expr, expr}
            auto openBrace = consume();
            switch (peek()->kind) {
                case TokenKind::CloseBrace:
                    expr = alloc.emplace<EmptyQueueExpressionSyntax>(openBrace, consume());
                    break;
                case TokenKind::LeftShift:
                case TokenKind::RightShift:
                    expr = parseStreamConcatenation(openBrace);
                    break;
                default: {
                    auto first = parseExpression();
                    if (!peek(TokenKind::OpenBrace))
                        expr = parseConcatenation(openBrace, first);
                    else {
                        auto openBraceInner = consume();
                        auto concat = parseConcatenation(openBraceInner, nullptr);
                        auto closeBrace = expect(TokenKind::CloseBrace);
                        expr = alloc.emplace<MultipleConcatenationExpressionSyntax>(openBrace, first, concat, closeBrace);
                    }
                    break;
                }
            }
            break;
        }
        default:
            // either a name or implicit class handle, or an error
            // parseName() will insert a missing identifier token for the error case
            expr = parseName();
            break;
    }

    return parsePostfixExpression(expr);
}

ExpressionSyntax* Parser::parseInsideExpression(ExpressionSyntax* expr) {
    auto inside = expect(TokenKind::InsideKeyword);

    Token* openBrace;
    Token* closeBrace;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseSeparatedList<isPossibleInsideElement, isEndOfBracedList>(
        TokenKind::OpenBrace,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        openBrace,
        list,
        closeBrace,
        &Parser::parseInsideElement
    );
    return alloc.emplace<InsideExpressionSyntax>(expr, inside, openBrace, list, closeBrace);
}

ExpressionSyntax* Parser::parseInsideElement() {
    if (!peek(TokenKind::OpenBracket))
        return parseExpression();
    return parseElementSelect();
}

ConcatenationExpressionSyntax* Parser::parseConcatenation(Token* openBrace, ExpressionSyntax* first) {
    auto buffer = tosPool.get();
    if (first) {
        buffer.append(first);
        buffer.append(expect(TokenKind::Comma));
    }

    Token* closeBrace;
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        buffer,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        closeBrace,
        &Parser::parseExpression
    );

    return alloc.emplace<ConcatenationExpressionSyntax>(openBrace, buffer.copy(alloc), closeBrace);
}

StreamingConcatenationExpressionSyntax* Parser::parseStreamConcatenation(Token* openBrace) {
    auto op = consume();
    ExpressionSyntax* sliceSize = nullptr;
    if (!peek(TokenKind::OpenBrace))
        sliceSize = parseExpression();

    Token* openBraceInner;
    Token* closeBraceInner;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseSeparatedList<isPossibleExpressionOrComma, isEndOfBracedList>(
        TokenKind::OpenBrace,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        openBraceInner,
        list,
        closeBraceInner,
        &Parser::parseStreamExpression
    );

    auto closeBrace = expect(TokenKind::CloseBrace);
    return alloc.emplace<StreamingConcatenationExpressionSyntax>(
        openBrace,
        op,
        sliceSize,
        openBraceInner,
        list,
        closeBraceInner,
        closeBrace
    );
}

StreamExpressionSyntax* Parser::parseStreamExpression() {
    auto expr = parseExpression();

    StreamExpressionWithRange* withRange = nullptr;
    if (peek(TokenKind::WithKeyword)) {
        auto with = consume();
        withRange = alloc.emplace<StreamExpressionWithRange>(with, parseElementSelect());
    }

    return alloc.emplace<StreamExpressionSyntax>(expr, withRange);
}

ElementSelectSyntax* Parser::parseElementSelect() {
    auto openBracket = expect(TokenKind::OpenBracket);
    auto expr = parseExpression();

    SelectorSyntax* selector;
    switch (peek()->kind) {
        case TokenKind::Colon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::SimpleRangeSelect, expr, range, parseExpression());
            break;
        }
        case TokenKind::PlusColon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::AscendingRangeSelect, expr, range, parseExpression());
            break;
        }
        case TokenKind::MinusColon: {
            auto range = consume();
            selector = alloc.emplace<RangeSelectSyntax>(SyntaxKind::DescendingRangeSelect, expr, range, parseExpression());
            break;
        }
        default:
            selector = alloc.emplace<BitSelectSyntax>(expr);
            break;
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return alloc.emplace<ElementSelectSyntax>(openBracket, selector, closeBracket);
}

ExpressionSyntax* Parser::parsePostfixExpression(ExpressionSyntax* expr) {
    while (true) {
        switch (peek()->kind) {
            case TokenKind::OpenBracket:
                expr = alloc.emplace<ElementSelectExpressionSyntax>(expr, parseElementSelect());
                break;
            case TokenKind::Dot: {
                auto dot = consume();
                auto name = expect(TokenKind::Identifier);
                expr = alloc.emplace<MemberAccessExpressionSyntax>(expr, dot, name);
                break;
            }
            case TokenKind::OpenParenthesis:
                expr = alloc.emplace<InvocationExpressionSyntax>(expr, parseArgumentList());
                break;
            // can't have any other postfix expressions after inc/dec
            // TODO: parse attributes
            case TokenKind::DoublePlus:
                return alloc.emplace<PostfixUnaryExpressionSyntax>(SyntaxKind::PostincrementExpression, expr, ArrayRef<AttributeInstanceSyntax*>(nullptr), consume());
            case TokenKind::DoubleMinus:
                return alloc.emplace<PostfixUnaryExpressionSyntax>(SyntaxKind::PostdecrementExpression, expr, ArrayRef<AttributeInstanceSyntax*>(nullptr), consume());
            default:
                return expr;
        }
    }
}

NameSyntax* Parser::parseName() {
    NameSyntax* name = parseNamePart();

    auto kind = peek()->kind;
    while (kind == TokenKind::Dot || kind == TokenKind::DoubleColon) {
        // TODO: error if switching from dots back to colons
        auto separator = consume();
        name = alloc.emplace<ScopedNameSyntax>(name, separator, parseNamePart());
        kind = peek()->kind;
    }

    return name;
}

NameSyntax* Parser::parseNamePart() {
    switch (peek()->kind) {
        case TokenKind::UnitSystemName: return alloc.emplace<KeywordNameSyntax>(SyntaxKind::UnitScope, consume());
        case TokenKind::RootSystemName: return alloc.emplace<KeywordNameSyntax>(SyntaxKind::RootScope, consume());
        case TokenKind::LocalKeyword: return alloc.emplace<KeywordNameSyntax>(SyntaxKind::LocalScope, consume());
        case TokenKind::ThisKeyword: return alloc.emplace<KeywordNameSyntax>(SyntaxKind::ThisHandle, consume());
        case TokenKind::SuperKeyword: return alloc.emplace<KeywordNameSyntax>(SyntaxKind::SuperHandle, consume());
        default: {
            auto identifier = expect(TokenKind::Identifier);
            switch (peek()->kind) {
                case TokenKind::Hash: {
                    auto parameterValues = parseParameterValueAssignment();
                    return alloc.emplace<ClassNameSyntax>(identifier, parameterValues);
                }
                case TokenKind::OpenBracket: {
                    auto buffer = nodePool.getAs<ElementSelectSyntax*>();
                    do {
                        buffer.append(parseElementSelect());
                    } while (peek(TokenKind::OpenBracket));

                    return alloc.emplace<IdentifierSelectNameSyntax>(identifier, buffer.copy(alloc));
                }
                default: return alloc.emplace<IdentifierNameSyntax>(identifier);
            }
        }
    }
}

ParameterValueAssignmentSyntax* Parser::parseParameterValueAssignment() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();
    return alloc.emplace<ParameterValueAssignmentSyntax>(hash, parseArgumentList());
}

ArgumentListSyntax* Parser::parseArgumentList() {
    Token* openParen;
    Token* closeParen;
    ArrayRef<TokenOrSyntax> list = nullptr;

    parseSeparatedList<isPossibleArgument, isEndOfParenList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        openParen,
        list,
        closeParen,
        &Parser::parseArgument
    );

    return alloc.emplace<ArgumentListSyntax>(openParen, list, closeParen);
}

ArgumentSyntax* Parser::parseArgument() {
    // check for named arguments
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto innerOpenParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr = nullptr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = parseExpression();

        return alloc.emplace<NamedArgumentSyntax>(dot, name, innerOpenParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return alloc.emplace<OrderedArgumentSyntax>(parseExpression());
}

PatternSyntax* Parser::parsePattern() {
    switch (peek()->kind) {
        case TokenKind::DotStar:
            return alloc.emplace<WildcardPatternSyntax>(consume());
        case TokenKind::Dot: {
            auto dot = consume();
            return alloc.emplace<VariablePatternSyntax>(dot, expect(TokenKind::Identifier));
        }
        case TokenKind::TaggedKeyword: {
            auto tagged = consume();
            auto name = expect(TokenKind::Identifier);
            // TODO: optional trailing pattern
            return alloc.emplace<TaggedPatternSyntax>(tagged, name, nullptr);
        }
        case TokenKind::ApostropheOpenBrace:
            // TODO: assignment pattern
            break;
    }
    // otherwise, it's either an expression or an error (parseExpression will handle that for us)
    return alloc.emplace<ExpressionPatternSyntax>(parseExpression());
}

ConditionalPredicateSyntax* Parser::parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token*& end) {
    auto buffer = tosPool.get();
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        auto matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
        buffer.append(alloc.emplace<ConditionalPatternSyntax>(first, matchesClause));
    }
    else {
        buffer.append(alloc.emplace<ConditionalPatternSyntax>(first, nullptr));
        if (peek(TokenKind::TripleAnd))
            buffer.append(consume());
    }

    parseSeparatedList<isPossibleExpressionOrTripleAnd, isEndOfConditionalPredicate>(
        buffer,
        endKind,
        TokenKind::TripleAnd,
        end,
        &Parser::parseConditionalPattern
    );

    return alloc.emplace<ConditionalPredicateSyntax>(buffer.copy(alloc));
}

ConditionalPatternSyntax* Parser::parseConditionalPattern() {
    auto expr = parseExpression();
    
    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
    }

    return alloc.emplace<ConditionalPatternSyntax>(expr, matchesClause);
}

EventExpressionSyntax* Parser::parseEventExpression() {
    EventExpressionSyntax* left;
    switch (peek()->kind) {
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto expr = parseEventExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            left = alloc.emplace<ParenthesizedEventExpressionSyntax>(openParen, expr, closeParen);
            break;
        }
        case TokenKind::PosEdgeKeyword:
        case TokenKind::NegEdgeKeyword:
        case TokenKind::EdgeKeyword: {
            auto edge = consume();
            auto expr = parseExpression();

            IffClauseSyntax* iffClause = nullptr;
            if (peek(TokenKind::IffKeyword)) {
                auto iff = consume();
                iffClause = alloc.emplace<IffClauseSyntax>(iff, parseExpression());
            }
            left = alloc.emplace<SignalEventExpressionSyntax>(edge, expr, iffClause);
            break;
        }
        // TODO: sequence instances and undecorated signal expressions
        default:
            left = nullptr;
            break;
    }

    auto kind = peek()->kind;
    if (kind == TokenKind::Comma || kind == TokenKind::OrKeyword) {
        auto op = consume();
        left = alloc.emplace<BinaryEventExpressionSyntax>(left, op, parseEventExpression());
    }
    return left;
}

ExpressionSyntax* Parser::parseAssignmentExpression() {
    if (!peek(TokenKind::NewKeyword))
        return parseExpression();

    auto newKeyword = consume();
    auto kind = peek()->kind;

    if (kind == TokenKind::OpenBracket) {
        // new array
        auto openBracket = consume();
        auto sizeExpr = parseExpression();
        auto closeBracket = expect(TokenKind::CloseBracket);

        ParenthesizedExpressionSyntax* initializer = nullptr;
        if (peek(TokenKind::OpenParenthesis)) {
            auto openParen = consume();
            auto initializerExpr = parseExpression();
            initializer = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, initializerExpr, expect(TokenKind::CloseParenthesis));
        }
        return alloc.emplace<NewArrayExpressionSyntax>(newKeyword, openBracket, sizeExpr, closeBracket, initializer);
    }

    // new class
    ArgumentListSyntax* arguments = nullptr;
    if (kind == TokenKind::OpenParenthesis)
        arguments = parseArgumentList();

    // TODO: handle class scoped new
    return alloc.emplace<NewClassExpressionSyntax>(nullptr, newKeyword, arguments);
}

TimingControlSyntax* Parser::parseTimingControl(bool allowRepeat) {
    switch (peek()->kind) {
        case TokenKind::Hash: {
            auto hash = consume();
            ExpressionSyntax* delayValue;
            switch (peek()->kind) {
                case TokenKind::IntegerLiteral:
                case TokenKind::RealLiteral:
                case TokenKind::TimeLiteral:
                case TokenKind::OneStep: {
                    auto literal = consume();
                    delayValue = alloc.emplace<LiteralExpressionSyntax>(getLiteralExpression(literal->kind), literal);
                    break;
                }
                case TokenKind::OpenParenthesis: {
                    auto openParen = consume();
                    auto expr = parseMinTypMaxExpression();
                    auto closeParen = expect(TokenKind::CloseParenthesis);
                    delayValue = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, expr, closeParen);
                    break;
                }
                default:
                    delayValue = parseName();
                    break;
            }
            return alloc.emplace<DelayControlSyntax>(hash, delayValue);
        }
        case TokenKind::DoubleHash: {
            auto doubleHash = consume();
            ExpressionSyntax* delayValue;
            switch (peek()->kind) {
                case TokenKind::IntegerLiteral:
                    delayValue = alloc.emplace<LiteralExpressionSyntax>(SyntaxKind::IntegerLiteralExpression, consume());
                    break;
                case TokenKind::OpenParenthesis: {
                    auto openParen = consume();
                    auto expr = parseExpression();
                    auto closeParen = expect(TokenKind::CloseParenthesis);
                    delayValue = alloc.emplace<ParenthesizedExpressionSyntax>(openParen, expr, closeParen);
                    break;
                }
                default:
                    delayValue = alloc.emplace<IdentifierNameSyntax>(expect(TokenKind::Identifier));
                    break;
            }
            return alloc.emplace<CycleDelaySyntax>(doubleHash, delayValue);
        }
        case TokenKind::At: {
            auto at = consume();
            if (peek(TokenKind::OpenParenthesis)) {
                auto openParen = consume();
                auto eventExpr = parseEventExpression();
                auto closeParen = expect(TokenKind::CloseParenthesis);
                return alloc.emplace<EventControlWithExpressionSyntax>(at, alloc.emplace<ParenthesizedEventExpressionSyntax>(openParen, eventExpr, closeParen));
            }
            else if (peek(TokenKind::OpenParenthesisStarCloseParenthesis))
                return alloc.emplace<ParenImplicitEventControlSyntax>(at, consume());
            else
                return alloc.emplace<EventControlSyntax>(at, parseName());
        }
        case TokenKind::AtStar:
            return alloc.emplace<ImplicitEventControlSyntax>(consume());
        case TokenKind::RepeatKeyword: {
            if (!allowRepeat)
                return nullptr;
            auto repeat = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto expr = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            return alloc.emplace<RepeatedEventControlSyntax>(repeat, openParen, expr, closeParen, parseTimingControl(/* allowRepeat */ false));
        }
        default:
            return nullptr;
    }
}

Token* Parser::parseSigning() {
    switch (peek()->kind) {
        case TokenKind::SignedKeyword:
        case TokenKind::UnsignedKeyword:
            return consume();
        default:
            return nullptr;
    }
}

VariableDimensionSyntax* Parser::parseDimension() {
    if (!peek(TokenKind::OpenBracket))
        return nullptr;

    auto openBracket = consume();

    DimensionSpecifierSyntax* specifier = nullptr;
    switch (peek()->kind) {
        case TokenKind::CloseBracket:
            // empty specifier
            break;
        case TokenKind::Star:
            specifier = alloc.emplace<WildcardDimensionSpecifierSyntax>(consume());
            break;
        case TokenKind::Dollar: {
            auto dollar = consume();

            ColonExpressionClauseSyntax* colonExpressionClause = nullptr;
            if (peek(TokenKind::Colon)) {
                auto colon = consume();
                colonExpressionClause = alloc.emplace<ColonExpressionClauseSyntax>(colon, parseExpression());
            }
            specifier = alloc.emplace<QueueDimensionSpecifierSyntax>(dollar, colonExpressionClause);
            break;
        }
        default:
            // TODO: scan type or expression
            break;
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return alloc.emplace<VariableDimensionSyntax>(openBracket, specifier, closeBracket);
}

ArrayRef<VariableDimensionSyntax*> Parser::parseDimensionList() {
    auto buffer = nodePool.getAs<VariableDimensionSyntax*>();
    while (true) {
        auto dim = parseDimension();
        if (!dim)
            break;
        buffer.append(dim);
    }
    return buffer.copy(alloc);
}

DataTypeSyntax* Parser::parseDataType(bool allowImplicit) {
    auto kind = peek()->kind;
    auto type = getIntegerType(kind);
    if (type != SyntaxKind::Unknown) {
        auto keyword = consume();
        auto signing = parseSigning();
        return alloc.emplace<IntegerTypeSyntax>(type, keyword, signing, parseDimensionList());
    }

    type = getKeywordType(kind);
    if (type != SyntaxKind::Unknown)
        return alloc.emplace<KeywordTypeSyntax>(type, consume());

    if (kind == TokenKind::VirtualKeyword) {
        auto virtualKeyword = consume();
        auto interfaceKeyword = consumeIf(TokenKind::InterfaceKeyword);
        auto name = expect(TokenKind::Identifier);
        auto parameters = parseParameterValueAssignment();

        DotMemberClauseSyntax* modport = nullptr;
        if (peek(TokenKind::Dot)) {
            auto dot = consume();
            modport = alloc.emplace<DotMemberClauseSyntax>(dot, expect(TokenKind::Identifier));
        }
        return alloc.emplace<VirtualInterfaceTypeSyntax>(virtualKeyword, interfaceKeyword, name, parameters, modport);
    }

    // TODO: other data types, implicit, void, etc
    return nullptr;
}

StatementSyntax* Parser::parseBlockDeclaration() {
    auto attributes = parseAttributes();

    // TODO: other kinds of declarations besides data
    bool hasVar = false;
    auto modifiers = tokenPool.get();
    auto kind = peek()->kind;
    while (isDeclarationModifier(kind)) {
        // TODO: error on bad combination / ordering
        modifiers.append(consume());
        if (kind == TokenKind::VarKeyword)
            hasVar = true;
        kind = peek()->kind;
    }

    auto dataType = parseDataType(/* allowImplicit */ hasVar);
    auto declarators = tosPool.get();

    declarators.append(parseVariableDeclarator(/* isFirst */ true));

    Trivia skippedTokens;
    while (true) {
        kind = peek()->kind;
        if (kind == TokenKind::Semicolon)
            break;
        else if (kind == TokenKind::Comma) {
            declarators.append(prependTrivia(consume(), &skippedTokens));
            declarators.append(parseVariableDeclarator(/* isFirst */ false));
        }
        else if (skipBadTokens<isComma, isSemicolon>(&skippedTokens) == SkipAction::Abort)
            break;
    }

    auto semi = prependTrivia(expect(TokenKind::Semicolon), &skippedTokens);
    return alloc.emplace<DataDeclarationSyntax>(nullptr, attributes, modifiers.copy(alloc), dataType, declarators.copy(alloc), semi);
}

VariableDeclaratorSyntax* Parser::parseVariableDeclarator(bool isFirst) {
    auto name = expect(TokenKind::Identifier);

    // Give a better error message for cases like:
    // X x = 1, Y y = 2;
    // The second identifier would be treated as a variable name, which is confusing
    if (!isFirst && peek(TokenKind::Identifier)) {
        // TODO: error msg
    }

    auto dimensions = parseDimensionList();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = alloc.emplace<EqualsValueClauseSyntax>(equals, parseAssignmentExpression());
    }

    return alloc.emplace<VariableDeclaratorSyntax>(name, dimensions, initializer);
}

ArrayRef<AttributeInstanceSyntax*> Parser::parseAttributes() {
    auto buffer = nodePool.getAs<AttributeInstanceSyntax*>();
    while (peek(TokenKind::OpenParenthesisStar)) {
        Token* openParen;
        Token* closeParen;
        ArrayRef<TokenOrSyntax> list = nullptr;

        parseSeparatedList<isIdentifierOrComma, isEndOfAttribute>(
            TokenKind::OpenParenthesisStar,
            TokenKind::StarCloseParenthesis,
            TokenKind::Comma,
            openParen,
            list,
            closeParen,
            &Parser::parseAttributeSpec
        );

        buffer.append(alloc.emplace<AttributeInstanceSyntax>(openParen, list, closeParen));
    }
    return buffer.copy(alloc);
}

AttributeSpecSyntax* Parser::parseAttributeSpec() {
    auto name = expect(TokenKind::Identifier);

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = alloc.emplace<EqualsValueClauseSyntax>(equals, parseExpression());
    }

    return alloc.emplace<AttributeSpecSyntax>(name, initializer);
}

bool Parser::isPossibleBlockDeclaration() {
    int index = 0;
    while (peek(index)->kind == TokenKind::OpenParenthesisStar) {
        // scan over attributes
        while (true) {
            auto kind = peek(++index)->kind;
            if (kind == TokenKind::EndOfFile)
                return false;
            if (kind == TokenKind::OpenParenthesisStar || kind == TokenKind::StarCloseParenthesis)
                break;
        }
    }

    // decide whether a statement is a declaration or the start of an expression
    auto kind = peek(index++)->kind;
    switch (kind) {
        // some tokens unambiguously start a declaration
        case TokenKind::VarKeyword:
        case TokenKind::AutomaticKeyword:
        case TokenKind::StaticKeyword:
        case TokenKind::CHandleKeyword:
        case TokenKind::VirtualKeyword:
        case TokenKind::EventKeyword:
        case TokenKind::StructKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::EnumKeyword:
        case TokenKind::TypedefKeyword:
        case TokenKind::ImportKeyword:
        case TokenKind::NetTypeKeyword:
        case TokenKind::LocalParamKeyword:
        case TokenKind::ParameterKeyword:
        case TokenKind::BindKeyword:
        case TokenKind::LetKeyword:
            return true;

        // some cases might be a cast expression
        case TokenKind::StringKeyword:
        case TokenKind::ConstKeyword:
        case TokenKind::BitKeyword:
        case TokenKind::LogicKeyword:
        case TokenKind::RegKeyword:
        case TokenKind::ByteKeyword:
        case TokenKind::ShortIntKeyword:
        case TokenKind::IntKeyword:
        case TokenKind::LongIntKeyword:
        case TokenKind::IntegerKeyword:
        case TokenKind::TimeKeyword:
        case TokenKind::ShortRealKeyword:
        case TokenKind::RealKeyword:
        case TokenKind::RealTimeKeyword: {
            auto next = peek(index)->kind;
            return next != TokenKind::Apostrophe && next != TokenKind::ApostropheOpenBrace;
        }
    }

    // scan through tokens until we find one that disambiguates
    if (kind != TokenKind::Identifier && kind != TokenKind::UnitSystemName)
        return false;

    do {
        if (peek(++index)->kind == TokenKind::Hash) {
            // scan parameter value assignment
            if (peek(++index)->kind != TokenKind::OpenParenthesis)
                return false;
            index++;
            if (!scanTypePart(index, TokenKind::OpenParenthesis, TokenKind::CloseParenthesis))
                return false;
        }
    } while (peek(index)->kind == TokenKind::DoubleColon);

    // might be a list of dimensions here
    while (peek(index)->kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return false;
    }

    // next token is the decider; declarations must have an identifier here
    return peek(index)->kind == TokenKind::Identifier;
}

bool Parser::scanTypePart(int& index, TokenKind start, TokenKind end) {
    int nesting = 1;
    while (true) {
        auto kind = peek(index)->kind;
        if (isNotInType(kind))
            return false;

        index++;
        if (kind == start)
            nesting++;
        else if (kind == end) {
            nesting--;
            if (nesting <= 0)
                return true;
        }
    }
}

// this is a generalized method for parsing a comma separated list of things
// with bookend tokens in a way that robustly handles bad tokens
template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
void Parser::parseSeparatedList(
    TokenKind openKind,
    TokenKind closeKind,
    TokenKind separatorKind,
    Token*& openToken,
    ArrayRef<TokenOrSyntax>& list,
    Token*& closeToken,
    TParserFunc&& parseItem
) {
    openToken = expect(openKind);

    auto buffer = tosPool.get();
    parseSeparatedList<IsExpected, IsEnd, TParserFunc>(buffer, closeKind, separatorKind, closeToken, std::forward<TParserFunc>(parseItem));
    list = buffer.copy(alloc);
}

template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
void Parser::parseSeparatedList(
    Buffer<TokenOrSyntax>& buffer,
    TokenKind closeKind,
    TokenKind separatorKind,
    Token*& closeToken,
    TParserFunc&& parseItem
) {
    Trivia skippedTokens;
    auto current = peek();
    if (!IsEnd(current->kind)) {
        while (true) {
            if (IsExpected(current->kind)) {
                buffer.append(prependTrivia((this->*parseItem)(), &skippedTokens));
                while (true) {
                    current = peek();
                    if (IsEnd(current->kind))
                        break;

                    if (IsExpected(current->kind)) {
                        buffer.append(prependTrivia(expect(separatorKind), &skippedTokens));
                        buffer.append((this->*parseItem)());
                        continue;
                    }

                    if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens) == SkipAction::Abort)
                        break;
                }
                // found the end
                break;
            }
            else if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens) == SkipAction::Abort)
                break;
            else
                current = peek();
        }
    }
    closeToken = prependTrivia(expect(closeKind), &skippedTokens);
}

template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
Parser::SkipAction Parser::skipBadTokens(Trivia* skippedTokens) {
    auto tokens = tokenPool.get();
    auto result = SkipAction::Continue;
    auto current = peek();
    while (!IsExpected(current->kind)) {
        if (current->kind == TokenKind::EndOfFile || IsAbort(current->kind)) {
            result = SkipAction::Abort;
            break;
        }
        tokens.append(consume());
        current = peek();
    }

    if (tokens.empty())
        *skippedTokens = Trivia();
    else
        *skippedTokens = Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc));

    return result;
}

SyntaxNode* Parser::prependTrivia(SyntaxNode* node, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && node)
        prependTrivia(node->getFirstToken(), trivia);
    return node;
}

Token* Parser::prependTrivia(Token* token, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && token) {
        auto buffer = triviaPool.get();
        buffer.append(*trivia);
        buffer.appendRange(token->trivia);
        token->trivia = buffer.copy(alloc);

        *trivia = Trivia();
    }
    return token;
}

void Parser::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

}

// a bunch of local helpers to check various token kinds
namespace {

using namespace slang;

bool isPossibleArgument(TokenKind kind) {
    // allow a comma here to handle cases like:  foo(, 3);
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isComma(TokenKind kind) {
    return kind == TokenKind::Comma;
}

bool isSemicolon(TokenKind kind) {
    return kind == TokenKind::Semicolon;
}

bool isIdentifierOrComma(TokenKind kind) {
    return kind == TokenKind::Identifier || kind == TokenKind::Comma;
}

bool isPossibleExpressionOrComma(TokenKind kind) {
    return kind == TokenKind::Comma || isPossibleExpression(kind);
}

bool isPossibleExpressionOrTripleAnd(TokenKind kind) {
    return kind == TokenKind::TripleAnd || isPossibleExpression(kind);
}

bool isPossibleInsideElement(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenBracket:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossiblePattern(TokenKind kind) {
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::DotStar:
        case TokenKind::ApostropheOpenBrace:
            return true;
        default:
            return isPossibleExpression(kind);
    }
}

bool isPossibleDelayOrEventControl(TokenKind kind) {
    switch (kind) {
        case TokenKind::Hash:
        case TokenKind::At:
        case TokenKind::AtStar:
        case TokenKind::RepeatKeyword:
            return true;
    }
    return false;
}

bool isEndKeyword(TokenKind kind) {
    switch (kind) {
        case TokenKind::EndKeyword:
        case TokenKind::EndCaseKeyword:
        case TokenKind::EndCheckerKeyword:
        case TokenKind::EndClassKeyword:
        case TokenKind::EndClockingKeyword:
        case TokenKind::EndConfigKeyword:
        case TokenKind::EndFunctionKeyword:
        case TokenKind::EndGenerateKeyword:
        case TokenKind::EndGroupKeyword:
        case TokenKind::EndInterfaceKeyword:
        case TokenKind::EndModuleKeyword:
        case TokenKind::EndPackageKeyword:
        case TokenKind::EndPrimitiveKeyword:
        case TokenKind::EndProgramKeyword:
        case TokenKind::EndPropertyKeyword:
        case TokenKind::EndSpecifyKeyword:
        case TokenKind::EndSequenceKeyword:
        case TokenKind::EndTableKeyword:
        case TokenKind::EndTaskKeyword:
            return true;
    }
    return false;
}

bool isDeclarationModifier(TokenKind kind) {
    switch (kind) {
        case TokenKind::ConstKeyword:
        case TokenKind::VarKeyword:
        case TokenKind::StaticKeyword:
        case TokenKind::AutomaticKeyword:
            return true;
    }
    return false;
}

bool isEndOfParenList(TokenKind kind) {
    return kind == TokenKind::CloseParenthesis || kind == TokenKind::Semicolon;
}

bool isEndOfBracedList(TokenKind kind) {
    return kind == TokenKind::CloseBrace || kind == TokenKind::Semicolon;
}

bool isEndOfCaseItem(TokenKind kind) {
    return kind == TokenKind::Colon || kind == TokenKind::Semicolon;
}

bool isEndOfConditionalPredicate(TokenKind kind) {
    return kind == TokenKind::Question || kind == TokenKind::CloseParenthesis || kind == TokenKind::BeginKeyword || kind == TokenKind::Semicolon;
}

bool isEndOfAttribute(TokenKind kind) {
    switch (kind) {
        case TokenKind::StarCloseParenthesis:
            // these indicate a missing *) somewhere
        case TokenKind::Semicolon:
        case TokenKind::PrimitiveKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::PackageKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::GenerateKeyword:
        case TokenKind::ModuleKeyword:
        case TokenKind::ClassKeyword:
            return true;
        default:
            return false;
    }
}

bool isNotInType(TokenKind kind) {
    switch (kind) {
        case TokenKind::Semicolon:
        case TokenKind::EndOfFile:
            return true;
        default:
            return isEndKeyword(kind);
    }
}

}