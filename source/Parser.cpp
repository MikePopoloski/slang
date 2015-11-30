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
bool isCloseBrace(TokenKind kind);
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
bool isEndOfParameterList(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);

}

namespace slang {

Parser::Parser(Lexer& lexer) :
    lexer(lexer),
    alloc(lexer.getPreprocessor().getAllocator()),
    diagnostics(lexer.getPreprocessor().getDiagnostics()),
    window(lexer) {
}

CompilationUnitSyntax* Parser::parseCompilationUnit() {
    auto members = parseMemberList(TokenKind::EndOfFile);
    auto eof = expect(TokenKind::EndOfFile);
    return alloc.emplace<CompilationUnitSyntax>(members, eof);
}

ModuleDeclarationSyntax* Parser::parseModule() {
    return parseModule(parseAttributes());
}

ModuleDeclarationSyntax* Parser::parseModule(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto header = parseModuleHeader();
    auto endKind = getModuleEndKind(header->moduleKeyword->kind);
    auto members = parseMemberList(endKind);
    auto endmodule = expect(endKind);
    return alloc.emplace<ModuleDeclarationSyntax>(
        getModuleDeclarationKind(header->moduleKeyword->kind),
        attributes,
        header,
        members,
        endmodule,
        parseNamedBlockClause()
    );
}

ModuleHeaderSyntax* Parser::parseModuleHeader() {
    auto moduleKeyword = consume();

    Token* lifetime = nullptr;
    auto kind = peek()->kind;
    if (kind == TokenKind::StaticKeyword || kind == TokenKind::AutomaticKeyword)
        lifetime = consume();

    auto name = expect(TokenKind::Identifier);
    auto imports = parsePackageImports();

    ParameterPortListSyntax* parameterList = nullptr;
    if (peek(TokenKind::Hash)) {
        auto hash = consume();
        
        Token* openParen;
        Token* closeParen;
        ArrayRef<TokenOrSyntax> parameters = nullptr;
        parseSeparatedList<isPossibleParameter, isEndOfParameterList>(
            TokenKind::OpenParenthesis,
            TokenKind::CloseParenthesis,
            TokenKind::Comma,
            openParen,
            parameters,
            closeParen,
            &Parser::parseParameterPort
        );

        parameterList = alloc.emplace<ParameterPortListSyntax>(hash, openParen, parameters, closeParen);
    }

    PortListSyntax* ports = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        auto openParen = consume();
        if (peek(TokenKind::DotStar)) {
            auto dotStar = consume();
            ports = alloc.emplace<WildcardPortListSyntax>(openParen, dotStar, expect(TokenKind::CloseParenthesis));
        }
        else if (peek(TokenKind::CloseParenthesis)) {
            ports = alloc.emplace<AnsiPortListSyntax>(openParen, nullptr, consume());
        }
        else if (isNonAnsiPort()) {
            Token* closeParen;
            auto buffer = tosPool.get();
            parseSeparatedList<isPossibleNonAnsiPort, isEndOfParenList>(buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, &Parser::parseNonAnsiPort);

            ports = alloc.emplace<NonAnsiPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
        }
        else {
            Token* closeParen;
            auto buffer = tosPool.get();
            parseSeparatedList<isPossibleAnsiPort, isEndOfParenList>(buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, &Parser::parseAnsiPort);

            ports = alloc.emplace<AnsiPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
        }
    }

    auto semi = expect(TokenKind::Semicolon);
    return alloc.emplace<ModuleHeaderSyntax>(getModuleHeaderKind(moduleKeyword->kind), moduleKeyword, lifetime, name, imports, parameterList, ports, semi);
}

NonAnsiPortSyntax* Parser::parseNonAnsiPort() {
    // TODO: error if unsupported expressions are used here
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto openParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = parsePrimaryExpression();

        return alloc.emplace<ExplicitNonAnsiPortSyntax>(dot, name, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return alloc.emplace<ImplicitNonAnsiPortSyntax>(parsePrimaryExpression());
}

PortHeaderSyntax* Parser::parsePortHeader(Token* direction) {
    auto kind = peek()->kind;
    if (isNetType(kind)) {
        auto netType = consume();
        return alloc.emplace<NetPortHeaderSyntax>(direction, netType, parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::InterfaceKeyword) {
        // TODO: error if direction is given
        auto keyword = consume();
        return alloc.emplace<InterfacePortHeaderSyntax>(keyword, parseDotMemberClause());
    }

    if (kind == TokenKind::InterconnectKeyword) {
        auto keyword = consume();
        // TODO: parse implicit data type only
        return alloc.emplace<InterconnectPortHeaderSyntax>(direction, keyword, nullptr);
    }

    if (kind == TokenKind::VarKeyword) {
        auto varKeyword = consume();
        return alloc.emplace<VariablePortHeaderSyntax>(direction, varKeyword, parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::Identifier) {
        // could be a bunch of different things here; scan ahead to see
        if (peek(1)->kind == TokenKind::Dot && peek(2)->kind == TokenKind::Identifier && peek(3)->kind == TokenKind::Identifier) {
            auto name = consume();
            return alloc.emplace<InterfacePortHeaderSyntax>(name, parseDotMemberClause());
        }
        
        if (isPlainPortName()) {
            // no header
            return nullptr;
        }
        return alloc.emplace<VariablePortHeaderSyntax>(direction, nullptr, parseDataType(/* allowImplicit */ false));
    }

    // assume we have some kind of data type here
    return alloc.emplace<VariablePortHeaderSyntax>(direction, nullptr, parseDataType(/* allowImplicit */ true));
}

AnsiPortSyntax* Parser::parseAnsiPort() {
    auto attributes = parseAttributes();
    auto kind = peek()->kind;

    Token* direction = nullptr;
    if (isPortDirection(kind)) {
        direction = consume();
        kind = peek()->kind;
    }

    if (kind == TokenKind::Dot) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto openParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = parseExpression();

        return alloc.emplace<ExplicitAnsiPortSyntax>(attributes, direction, dot, name, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    auto header = parsePortHeader(direction);
    auto declarator = parseVariableDeclarator<false>(/* isFirst */ true);
    return alloc.emplace<ImplicitAnsiPortSyntax>(attributes, header, declarator);
}

PortDeclarationSyntax* Parser::parsePortDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    Token* direction = nullptr;
    if (isPortDirection(peek()->kind))
        direction = consume();

    auto header = parsePortHeader(direction);
    auto declarator = parseVariableDeclarator<false>(/* isFirst */ true);
    return alloc.emplace<PortDeclarationSyntax>(attributes, header, declarator, expect(TokenKind::Semicolon));
}

bool Parser::isPlainPortName() {
    int index = 1;
    while (peek(index)->kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInPortReference>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return true; // if we see nonsense, we'll recover by pretending this is a plain port
    }

    auto kind = peek(index)->kind;
    return kind == TokenKind::Equals || kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis;
}

bool Parser::isNonAnsiPort() {
    auto kind = peek()->kind;
    if (kind == TokenKind::Dot || kind == TokenKind::OpenBrace)
        return true;

    if (kind != TokenKind::Identifier)
        return false;

    // this might be a port name or the start of a data type
    // scan over select expressions until we find out
    int index = 1;
    while (true) {
        kind = peek(index++)->kind;
        if (kind == TokenKind::Dot) {
            if (peek(index++)->kind != TokenKind::Identifier)
                return false;
        }
        else if (kind == TokenKind::OpenBracket) {
            if (!scanTypePart<isNotInPortReference>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
                return false;
        }
        else {
            // found the end; comma or close paren means this is a non-ansi port
            return kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis;
        }
    }
}

MemberSyntax* Parser::parseMember() {
    auto attributes = parseAttributes();

    if (isHierarchyInstantiation())
        return parseHierarchyInstantiation(attributes);
    if (isPortDeclaration())
        return parsePortDeclaration(attributes);
    if (isNetDeclaration())
        return parseNetDeclaration(attributes);
    if (isVariableDeclaration())
        return parseVariableDeclaration(attributes);

    // TODO: error on attributes that don't attach to a valid construct

    switch (peek()->kind) {
        case TokenKind::GenerateKeyword: {
            auto keyword = consume();
            auto members = parseMemberList(TokenKind::EndGenerateKeyword);
            return alloc.emplace<GenerateBlockSyntax>(attributes, keyword, members, expect(TokenKind::EndGenerateKeyword));
        }

        case TokenKind::SpecifyKeyword:

        case TokenKind::TimeUnitKeyword:
        case TokenKind::TimePrecisionKeyword:
            return parseTimeUnitsDeclaration(attributes);

        case TokenKind::ModuleKeyword:
        case TokenKind::MacromoduleKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::InterfaceKeyword:
            // modules, interfaces, and programs share the same syntax
            return parseModule(attributes);

        case TokenKind::SpecParamKeyword:
        case TokenKind::DefParamKeyword:
        case TokenKind::Identifier:
        case TokenKind::BindKeyword:
        case TokenKind::AssignKeyword:
        case TokenKind::AliasKeyword:

        case TokenKind::InitialKeyword:
        case TokenKind::FinalKeyword:
        case TokenKind::AlwaysKeyword:
        case TokenKind::AlwaysCombKeyword:
        case TokenKind::AlwaysFFKeyword:
        case TokenKind::AlwaysLatchKeyword: {
            auto keyword = consume();
            return alloc.emplace<ProceduralBlockSyntax>(getProceduralBlockKind(keyword->kind), attributes, keyword, parseStatement());
        }
        case TokenKind::ForKeyword:
        case TokenKind::IfKeyword:
        case TokenKind::CaseKeyword:
        case TokenKind::GenVarKeyword:
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::RefKeyword:
            break;

        case TokenKind::TaskKeyword:
        case TokenKind::FunctionKeyword:
        case TokenKind::CheckerKeyword:
            break;
    }
}

ArrayRef<MemberSyntax*> Parser::parseMemberList(TokenKind endKind) {
    auto buffer = nodePool.getAs<MemberSyntax*>();
    while (true) {
        auto kind = peek()->kind;
        if (kind == TokenKind::EndOfFile || kind == endKind)
            break;

        // TODO: error checking

        buffer.append(parseMember());
    }
    return buffer.copy(alloc);
}

TimeUnitsDeclarationSyntax* Parser::parseTimeUnitsDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto kind = peek()->kind;
    if (kind != TokenKind::TimeUnitKeyword && kind != TokenKind::TimePrecisionKeyword)
        return nullptr;

    auto keyword = consume();
    auto time = expect(TokenKind::TimeLiteral);

    DividerClauseSyntax* divider = nullptr;
    if (peek(TokenKind::Slash)) {
        auto divide = consume();
        divider = alloc.emplace<DividerClauseSyntax>(divide, expect(TokenKind::TimeLiteral));
    }

    return alloc.emplace<TimeUnitsDeclarationSyntax>(attributes, keyword, time, divider, expect(TokenKind::Semicolon));
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
        case TokenKind::ForKeyword:
            return parseForLoopStatement(label, attributes);
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

    // everything else is some kind of expression
    // TODO: expand this to other kinds of expression statements
    if (isPossibleExpression(peek()->kind))
        return parseAssignmentStatement(label, attributes);

    return nullptr;
}

ConditionalStatementSyntax* Parser::parseConditionalStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority) {
    auto ifKeyword = expect(TokenKind::IfKeyword);
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token* closeParen;
    auto predicate = parseConditionalPredicate(parseSubExpression<false>(0), TokenKind::CloseParenthesis, closeParen);
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

ForInitializerSyntax* Parser::parseForInitializer() {
    if (isVariableDeclaration()) {
        auto varKeyword = consumeIf(TokenKind::VarKeyword);
        auto type = parseDataType(/* allowImplicit */ false);
        return alloc.emplace<ForVariableDeclarationSyntax>(varKeyword, type, parseVariableDeclarator<true>(/* isFirst */ true));
    }

    auto left = parseExpression();
    auto equals = expect(TokenKind::Equals);
    auto right = parseExpression();
    return alloc.emplace<ForVariableAssignmentSyntax>(left, equals, right);
}

ForLoopStatementSyntax* Parser::parseForLoopStatement(StatementLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto forKeyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);

    Token* semi1;
    auto initializers = tosPool.get();
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfParenList>(initializers, TokenKind::Semicolon, TokenKind::Comma, semi1, &Parser::parseForInitializer);

    auto stopExpr = parseExpression();
    auto semi2 = expect(TokenKind::Semicolon);

    Token* closeParen;
    auto steps = tosPool.get();
    parseSeparatedList<isPossibleExpressionOrComma, isEndOfParenList>(steps, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, &Parser::parseExpression);

    return alloc.emplace<ForLoopStatementSyntax>(
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

        auto expr = parseAssignmentExpression<false>();
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

    auto buffer = nodePool.get();
    auto kind = peek()->kind;
    while (!isEndKeyword(kind) && kind != TokenKind::EndOfFile) {
        if (isVariableDeclaration())
            buffer.append(parseVariableDeclaration(parseAttributes()));
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
    return parseSubExpression<true>(0);
}

ExpressionSyntax* Parser::parseMinTypMaxExpression() {
    ExpressionSyntax* first = parseSubExpression<true>(0);
    if (!peek(TokenKind::Colon))
        return first;

    auto colon1 = consume();
    auto typ = parseSubExpression<true>(0);
    auto colon2 = expect(TokenKind::Colon);
    auto max = parseSubExpression<true>(0);

    return alloc.emplace<MinTypMaxExpressionSyntax>(first, colon1, typ, colon2, max);
}

template<bool AllowPatternMatch>
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
        ExpressionSyntax* operand = parseSubExpression<AllowPatternMatch>(newPrecedence);
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
            auto rightOperand = parseSubExpression<AllowPatternMatch>(newPrecedence);
            leftOperand = alloc.emplace<BinaryExpressionSyntax>(opKind, leftOperand, opToken, attributes, rightOperand);
        }
    }

    // can't nest pattern matching expressions
    if (AllowPatternMatch) {
        // if we see the matches keyword or &&& we're in a pattern conditional predicate
        // if we see a question mark, we were in a simple conditional predicate (at the precedence level one beneath logical-or)
        auto logicalOrPrecedence = getPrecedence(SyntaxKind::LogicalOrExpression);
        if (current->kind == TokenKind::MatchesKeyword || current->kind == TokenKind::TripleAnd ||
            (current->kind == TokenKind::Question && precedence < logicalOrPrecedence)) {

            Token* question;
            auto predicate = parseConditionalPredicate(leftOperand, TokenKind::Question, question);
            auto attributes = parseAttributes();
            auto left = parseSubExpression<AllowPatternMatch>(logicalOrPrecedence - 1);
            auto colon = expect(TokenKind::Colon);
            auto right = parseSubExpression<AllowPatternMatch>(logicalOrPrecedence - 1);
            leftOperand = alloc.emplace<ConditionalExpressionSyntax>(predicate, question, attributes, left, colon, right);
        }
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
            // possibilities here:
            // 1. data type
            // 2. qualified name
            // 3. implicit class handles
            // 4. error
            if (isPossibleDataType(kind) && kind != TokenKind::Identifier && kind != TokenKind::UnitSystemName)
                return parseDataType(/* allowImplicit */ false);

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
    auto selector = parseElementSelector();
    auto closeBracket = expect(TokenKind::CloseBracket);
    return alloc.emplace<ElementSelectSyntax>(openBracket, selector, closeBracket);
}

SelectorSyntax* Parser::parseElementSelector() {
    auto expr = parseExpression();
    switch (peek()->kind) {
        case TokenKind::Colon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::SimpleRangeSelect, expr, range, parseExpression());
        }
        case TokenKind::PlusColon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::AscendingRangeSelect, expr, range, parseExpression());
        }
        case TokenKind::MinusColon: {
            auto range = consume();
            return alloc.emplace<RangeSelectSyntax>(SyntaxKind::DescendingRangeSelect, expr, range, parseExpression());
        }
    }
    return alloc.emplace<BitSelectSyntax>(expr);
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
                expr = alloc.emplace<InvocationExpressionSyntax>(expr, nullptr, parseArgumentList());
                break;
            // can't have any other postfix expressions after inc/dec
            case TokenKind::DoublePlus:
            case TokenKind::DoubleMinus: {
                auto op = consume();
                return alloc.emplace<PostfixUnaryExpressionSyntax>(getUnaryPostfixExpression(op->kind), expr, nullptr, op);
            }
            case TokenKind::OpenParenthesisStar: {
                auto attributes = parseAttributes();
                switch (peek()->kind) {
                    case TokenKind::DoublePlus:
                    case TokenKind::DoubleMinus: {
                        auto op = consume();
                        return alloc.emplace<PostfixUnaryExpressionSyntax>(getUnaryPostfixExpression(op->kind), expr, attributes, op);
                    }
                    case TokenKind::OpenParenthesis:
                        expr = alloc.emplace<InvocationExpressionSyntax>(expr, attributes, parseArgumentList());
                        break;
                    default:
                        // otherwise, this has to be a function call without any arguments
                        expr = alloc.emplace<InvocationExpressionSyntax>(expr, attributes, nullptr);
                        break;
                }
                break;
            }
            default:
                return expr;
        }
    }
}

NameSyntax* Parser::parseName() {
    NameSyntax* name = parseNamePart();

    bool usedDot = false;
    bool reportedError = false;

    auto kind = peek()->kind;
    while (kind == TokenKind::Dot || kind == TokenKind::DoubleColon) {
        if (kind == TokenKind::Dot)
            usedDot = true;
        else if (usedDot && !reportedError) {
            reportedError = true;
            addError(DiagCode::ColonShouldBeDot);
        }

        auto separator = consume();
        name = alloc.emplace<ScopedNameSyntax>(name, separator, parseNamePart());
        kind = peek()->kind;
    }

    return name;
}

NameSyntax* Parser::parseNamePart() {
    auto kind = getKeywordNameExpression(peek()->kind);
    if (kind != SyntaxKind::Unknown)
        return alloc.emplace<KeywordNameSyntax>(kind, consume());

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
        default:
            return alloc.emplace<IdentifierNameSyntax>(identifier);
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
    return alloc.emplace<ExpressionPatternSyntax>(parseSubExpression<false>(0));
}

ConditionalPredicateSyntax* Parser::parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token*& end) {
    auto buffer = tosPool.get();

    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
    }

    buffer.append(alloc.emplace<ConditionalPatternSyntax>(first, matchesClause));
    if (peek(TokenKind::TripleAnd))
        buffer.append(consume());

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
    auto expr = parseSubExpression<false>(0);
    
    MatchesClauseSyntax* matchesClause = nullptr;
    if (peek(TokenKind::MatchesKeyword)) {
        auto matches = consume();
        matchesClause = alloc.emplace<MatchesClauseSyntax>(matches, parsePattern());
    }

    return alloc.emplace<ConditionalPatternSyntax>(expr, matchesClause);
}

EventExpressionSyntax* Parser::parseEventExpression() {
    EventExpressionSyntax* left;
    auto kind = peek()->kind;
    if (kind == TokenKind::OpenParenthesis) {
        auto openParen = consume();
        auto expr = parseEventExpression();
        auto closeParen = expect(TokenKind::CloseParenthesis);
        left = alloc.emplace<ParenthesizedEventExpressionSyntax>(openParen, expr, closeParen);
    }
    else {
        Token* edge = nullptr;
        if (kind == TokenKind::PosEdgeKeyword || kind == TokenKind::NegEdgeKeyword || kind == TokenKind::EdgeKeyword)
            edge = consume();

        // TODO: support sequence instances
        auto expr = parseExpression();

        IffClauseSyntax* iffClause = nullptr;
        if (peek(TokenKind::IffKeyword)) {
            auto iff = consume();
            iffClause = alloc.emplace<IffClauseSyntax>(iff, parseExpression());
        }
        left = alloc.emplace<SignalEventExpressionSyntax>(edge, expr, iffClause);
    }

    kind = peek()->kind;
    if (kind == TokenKind::Comma || kind == TokenKind::OrKeyword) {
        auto op = consume();
        left = alloc.emplace<BinaryEventExpressionSyntax>(left, op, parseEventExpression());
    }
    return left;
}

template<bool AllowMinTypeMax>
ExpressionSyntax* Parser::parseAssignmentExpression() {
    if (!peek(TokenKind::NewKeyword)) {
        if (AllowMinTypeMax)
            return parseMinTypMaxExpression();
        else
            return parseExpression();
    }

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
            specifier = alloc.emplace<RangeDimensionSpecifierSyntax>(parseElementSelector());
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

DotMemberClauseSyntax* Parser::parseDotMemberClause() {
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        return alloc.emplace<DotMemberClauseSyntax>(dot, expect(TokenKind::Identifier));
    }
    return nullptr;
}

StructUnionTypeSyntax* Parser::parseStructUnion(SyntaxKind syntaxKind) {
    auto keyword = consume();
    auto tagged = consumeIf(TokenKind::TaggedKeyword);
    auto packed = consumeIf(TokenKind::PackedKeyword);
    auto signing = parseSigning();
    auto openBrace = expect(TokenKind::OpenBrace);

    Token* closeBrace;
    auto buffer = nodePool.getAs<StructUnionMemberSyntax*>();

    if (openBrace->isMissing())
        closeBrace = Token::missing(alloc, TokenKind::CloseBrace);
    else {
        auto kind = peek()->kind;
        while (kind != TokenKind::CloseBrace && kind != TokenKind::EndOfFile) {
            auto attributes = parseAttributes();

            Token* randomQualifier = nullptr;
            switch (peek()->kind) {
                case TokenKind::RandKeyword:
                case TokenKind::RandCKeyword:
                    randomQualifier = consume();
            }

            auto type = parseDataType(/* allowImplicit */ false);

            Token* semi;
            auto declarators = parseVariableDeclarators<isSemicolon>(TokenKind::Semicolon, semi);

            buffer.append(alloc.emplace<StructUnionMemberSyntax>(attributes, randomQualifier, type, declarators, semi));
            kind = peek()->kind;
        }
        closeBrace = expect(TokenKind::CloseBrace);
    }

    return alloc.emplace<StructUnionTypeSyntax>(
        syntaxKind,
        keyword,
        tagged,
        packed,
        signing,
        openBrace,
        buffer.copy(alloc),
        closeBrace,
        parseDimensionList()
    );
}

EnumTypeSyntax* Parser::parseEnum() {
    auto keyword = consume();

    DataTypeSyntax* baseType = nullptr;
    if (!peek(TokenKind::OpenBrace))
        baseType = parseDataType(/* allowImplicit */ false);

    auto openBrace = expect(TokenKind::OpenBrace);

    Token* closeBrace;
    ArrayRef<TokenOrSyntax> declarators = nullptr;
    if (openBrace->isMissing())
        closeBrace = Token::missing(alloc, TokenKind::CloseBrace);
    else
        declarators = parseVariableDeclarators<isCloseBrace>(TokenKind::CloseBrace, closeBrace);

    return alloc.emplace<EnumTypeSyntax>(keyword, baseType, openBrace, declarators, closeBrace, parseDimensionList());
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

    switch (kind) {
        case TokenKind::StructKeyword: return parseStructUnion(SyntaxKind::StructType);
        case TokenKind::UnionKeyword: return parseStructUnion(SyntaxKind::UnionType);
        case TokenKind::EnumKeyword: return parseEnum();
        case TokenKind::VirtualKeyword: {
            auto virtualKeyword = consume();
            auto interfaceKeyword = consumeIf(TokenKind::InterfaceKeyword);
            auto name = expect(TokenKind::Identifier);
            auto parameters = parseParameterValueAssignment();
            return alloc.emplace<VirtualInterfaceTypeSyntax>(virtualKeyword, interfaceKeyword, name, parameters, parseDotMemberClause());
        }
        case TokenKind::UnitSystemName:
            return alloc.emplace<NamedTypeSyntax>(parseName());
        case TokenKind::TypeKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto expr = parseExpression();
            return alloc.emplace<TypeReferenceSyntax>(keyword, openParen, expr, expect(TokenKind::CloseParenthesis));
        }
    }

    if (kind == TokenKind::Identifier) {
        if (!allowImplicit)
            return alloc.emplace<NamedTypeSyntax>(parseName());
        else {
            int index = 1;
            if (scanDimensionList(index) && peek(index)->kind == TokenKind::Identifier)
                return alloc.emplace<NamedTypeSyntax>(parseName());
            return alloc.emplace<ImplicitTypeSyntax>(nullptr, nullptr);
        }
    }

    auto signing = parseSigning();
    auto dimensions = parseDimensionList();

    if (!allowImplicit)
        addError(DiagCode::ImplicitNotAllowed);

    return alloc.emplace<ImplicitTypeSyntax>(signing, dimensions);
}

MemberSyntax* Parser::parseNetDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto netType = consume();

    NetStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        // TODO: strength specifiers
    }

    Token* expansionHint = nullptr;
    if (peek(TokenKind::VectoredKeyword) || peek(TokenKind::ScalaredKeyword))
        expansionHint = consume();

    auto type = parseDataType(/* allowImplicit */ true);

    // TODO: delay control

    Token* semi;
    auto declarators = parseVariableDeclarators<isSemicolon>(TokenKind::Semicolon, semi);

    return alloc.emplace<NetDeclarationSyntax>(attributes, netType, strength, expansionHint, type, declarators, semi);
}

MemberSyntax* Parser::parseVariableDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword)) {
        auto parameter = parseParameterPort();
        return alloc.emplace<ParameterDeclarationStatementSyntax>(attributes, parameter, expect(TokenKind::Semicolon));
    }

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

    Token* semi;
    auto declarators = parseVariableDeclarators<isSemicolon>(TokenKind::Semicolon, semi);

    return alloc.emplace<DataDeclarationSyntax>(attributes, modifiers.copy(alloc), dataType, declarators, semi);
}

template<bool AllowMinTypMax>
VariableDeclaratorSyntax* Parser::parseVariableDeclarator(bool isFirst) {
    auto name = expect(TokenKind::Identifier);

    // Give a better error message for cases like:
    // X x = 1, Y y = 2;
    // The second identifier would be treated as a variable name, which is confusing
    if (!isFirst && peek(TokenKind::Identifier))
        addError(DiagCode::MultipleTypesInDeclaration);

    auto dimensions = parseDimensionList();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = alloc.emplace<EqualsValueClauseSyntax>(equals, parseAssignmentExpression<AllowMinTypMax>());
    }

    return alloc.emplace<VariableDeclaratorSyntax>(name, dimensions, initializer);
}

template<bool(*IsEnd)(TokenKind)>
ArrayRef<TokenOrSyntax> Parser::parseVariableDeclarators(TokenKind endKind, Token*& end) {
    auto buffer = tosPool.get();
    parseSeparatedListWithFirst<isIdentifierOrComma, IsEnd>(buffer, endKind, TokenKind::Comma, end, &Parser::parseVariableDeclarator<false>);

    return buffer.copy(alloc);
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

ArrayRef<PackageImportDeclarationSyntax*> Parser::parsePackageImports() {
    auto buffer = nodePool.getAs<PackageImportDeclarationSyntax*>();
    while (peek(TokenKind::ImportKeyword)) {
        auto keyword = consume();

        Token* semi;
        auto items = tosPool.get();
        parseSeparatedList<isIdentifierOrComma, isSemicolon>(
            items,
            TokenKind::Semicolon,
            TokenKind::Comma,
            semi,
            &Parser::parsePackageImportItem
        );

        buffer.append(alloc.emplace<PackageImportDeclarationSyntax>(keyword, items.copy(alloc), semi));
    }
    return buffer.copy(alloc);
}

PackageImportItemSyntax* Parser::parsePackageImportItem() {
    auto package = expect(TokenKind::Identifier);
    auto doubleColon = expect(TokenKind::DoubleColon);
    
    Token* item;
    if (peek(TokenKind::Star))
        item = consume();
    else
        item = expect(TokenKind::Identifier);

    return alloc.emplace<PackageImportItemSyntax>(package, doubleColon, item);
}

ParameterPortDeclarationSyntax* Parser::parseParameterPort() {
    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword)) {
        auto keyword = consume();

        if (peek(TokenKind::TypeKeyword)) {
            auto typeKeyword = consume();
            return alloc.emplace<TypeParameterDeclarationSyntax>(keyword, typeKeyword, parseVariableDeclarator<true>(/* isFirst */ true));
        }

        auto type = parseDataType(/* allowImplicit */ true);
        return alloc.emplace<ParameterDeclarationSyntax>(keyword, type, parseVariableDeclarator<true>(/* isFirst */ true));
    }

    if (peek(TokenKind::TypeKeyword)) {
        auto typeKeyword = consume();
        return alloc.emplace<TypeParameterDeclarationSyntax>(nullptr, typeKeyword, parseVariableDeclarator<true>(/* isFirst */ true));
    }

    // this is a normal parameter without the actual parameter keyword (stupid implicit nonsense)
    auto type = parseDataType(/* allowImplicit */ true);
    return alloc.emplace<ParameterDeclarationSyntax>(nullptr, type, parseVariableDeclarator<true>(/* isFirst */ true));
}

HierarchyInstantiationSyntax* Parser::parseHierarchyInstantiation(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto type = expect(TokenKind::Identifier);
    auto parameters = parseParameterValueAssignment();

    Token* semi;
    auto items = tosPool.get();
    parseSeparatedList<isIdentifierOrComma, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi, &Parser::parseHierarchicalInstance);

    return alloc.emplace<HierarchyInstantiationSyntax>(attributes, type, parameters, items.copy(alloc), semi);
}

HierarchicalInstanceSyntax* Parser::parseHierarchicalInstance() {
    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    Token* openParen;
    Token* closeParen;
    ArrayRef<TokenOrSyntax> items = nullptr;

    parseSeparatedList<isPossiblePortConnection, isEndOfParenList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        openParen,
        items,
        closeParen,
        &Parser::parsePortConnection
    );

    return alloc.emplace<HierarchicalInstanceSyntax>(name, dimensions, openParen, items, closeParen);
}

PortConnectionSyntax* Parser::parsePortConnection() {
    auto attributes = parseAttributes();

    if (peek(TokenKind::DotStar))
        return alloc.emplace<WildcardPortConnectionSyntax>(attributes, consume());

    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);

        ParenthesizedExpressionSyntax* parenExpr = nullptr;
        if (peek(TokenKind::OpenParenthesis)) {
            auto innerOpenParen = consume();
            ExpressionSyntax* expr = nullptr;
            if (!peek(TokenKind::CloseParenthesis))
                expr = parseExpression();

            parenExpr = alloc.emplace<ParenthesizedExpressionSyntax>(innerOpenParen, expr, expect(TokenKind::CloseParenthesis));
        }
        return alloc.emplace<NamedPortConnectionSyntax>(attributes, dot, name, parenExpr);
    }
    return alloc.emplace<OrderedPortConnectionSyntax>(attributes, parseExpression());
}

bool Parser::isPortDeclaration() {
    // TODO: check for interface port declaration
    return isPortDirection(peek()->kind);
}

bool Parser::isNetDeclaration() {
    // TODO: other net types
    return isNetType(peek()->kind);
}

bool Parser::isVariableDeclaration() {
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

    while (true) {
        if (peek(index)->kind == TokenKind::Hash) {
            // scan parameter value assignment
            if (peek(++index)->kind != TokenKind::OpenParenthesis)
                return false;
            index++;
            if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis, TokenKind::CloseParenthesis))
                return false;
        }

        if (peek(index)->kind != TokenKind::DoubleColon)
            break;

        index++;
        if (peek(index++)->kind != TokenKind::Identifier)
            return false;
    }

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // next token is the decider; declarations must have an identifier here
    return peek(index)->kind == TokenKind::Identifier;
}

bool Parser::isHierarchyInstantiation() {
    int index = 0;
    if (peek(index++)->kind != TokenKind::Identifier)
        return false;

    // skip over optional parameter value assignment
    if (peek(index)->kind == TokenKind::Hash) {
        if (peek(++index)->kind != TokenKind::OpenParenthesis)
            return false;
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis, TokenKind::CloseParenthesis))
            return false;
    }

    if (peek(index++)->kind != TokenKind::Identifier)
        return false;

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // a parenthesis here means we're definitely doing an instantiation
    return peek(index)->kind == TokenKind::OpenParenthesis;
}

bool Parser::scanDimensionList(int& index) {
    while (peek(index)->kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return false;
    }
    return true;
}

template<bool(*IsEnd)(TokenKind)>
bool Parser::scanTypePart(int& index, TokenKind start, TokenKind end) {
    int nesting = 1;
    while (true) {
        auto kind = peek(index)->kind;
        if (IsEnd(kind))
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
                        buffer.append(prependTrivia((this->*parseItem)(), &skippedTokens));
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

// this variant passes a boolean isFirst argument to the parse function
// there is an annoying duplication of code here with parseSeparatedList

template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
void Parser::parseSeparatedListWithFirst(
    Buffer<TokenOrSyntax>& buffer,
    TokenKind closeKind,
    TokenKind separatorKind,
    Token*& closeToken,
    TParserFunc&& parseItem
) {
    Trivia skippedTokens;
    parseSeparatedListWithFirst<IsExpected, IsEnd>(buffer, separatorKind, &skippedTokens, std::forward<TParserFunc>(parseItem));

    closeToken = prependTrivia(expect(closeKind), &skippedTokens);
}

template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
void Parser::parseSeparatedListWithFirst(
    Buffer<TokenOrSyntax>& buffer,
    TokenKind separatorKind,
    Trivia* skippedTokens,
    TParserFunc&& parseItem
) {
    auto current = peek();
    if (!IsEnd(current->kind)) {
        while (true) {
            if (IsExpected(current->kind)) {
                buffer.append(prependTrivia((this->*parseItem)(true), skippedTokens));
                while (true) {
                    current = peek();
                    if (IsEnd(current->kind))
                        break;

                    if (IsExpected(current->kind)) {
                        buffer.append(prependTrivia(expect(separatorKind), skippedTokens));
                        buffer.append(prependTrivia((this->*parseItem)(false), skippedTokens));
                        continue;
                    }

                    if (skipBadTokens<IsExpected, IsEnd>(skippedTokens) == SkipAction::Abort)
                        break;
                }
                // found the end
                break;
            }
            else if (skipBadTokens<IsExpected, IsEnd>(skippedTokens) == SkipAction::Abort)
                break;
            else
                current = peek();
        }
    }
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

template<typename T>
void Parser::prependTrivia(ArrayRef<T*> list, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && !list.empty())
        prependTrivia(*list.begin(), trivia);
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

bool isPossibleNonAnsiPort(TokenKind kind) {
    switch (kind) {
        case TokenKind::Dot:
        case TokenKind::Comma:
        case TokenKind::Identifier:
        case TokenKind::OpenBrace:
            return true;
        default:
            return false;
    }
}

bool isPossibleAnsiPort(TokenKind kind) {
    switch (kind) {
        case TokenKind::InterconnectKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::Identifier:
        case TokenKind::Dot:
        case TokenKind::Comma:
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::RefKeyword:
        case TokenKind::VarKeyword:
            return true;
    }
    return isNetType(kind) || isPossibleDataType(kind);
}

bool isComma(TokenKind kind) {
    return kind == TokenKind::Comma;
}

bool isSemicolon(TokenKind kind) {
    return kind == TokenKind::Semicolon;
}

bool isCloseBrace(TokenKind kind) {
    return kind == TokenKind::CloseBrace;
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

bool isPossibleParameter(TokenKind kind) {
    switch (kind) {
        case TokenKind::ParameterKeyword:
        case TokenKind::LocalParamKeyword:
        case TokenKind::TypeKeyword:
        case TokenKind::Comma:
            return true;
    }
    return isPossibleDataType(kind);
}

bool isPossiblePortConnection(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenParenthesisStar:
        case TokenKind::DotStar:
        case TokenKind::Dot:
        case TokenKind::Comma:
            return true;
        default:
            return isPossibleExpression(kind);
    }
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

bool isEndOfParameterList(TokenKind kind) {
    return kind == TokenKind::CloseParenthesis || kind == TokenKind::OpenParenthesis || kind == TokenKind::Semicolon;
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

bool isNotInPortReference(TokenKind kind) {
    return kind == TokenKind::Semicolon || kind == TokenKind::EndOfFile;
}

}