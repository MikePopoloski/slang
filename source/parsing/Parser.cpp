//------------------------------------------------------------------------------
// Parser.cpp
// SystemVerilog language parser.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/parsing/Parser.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Preprocessor.h"

namespace slang {

Parser::Parser(Preprocessor& preprocessor, const Bag& options) :
    ParserBase::ParserBase(preprocessor), factory(alloc),
    parseOptions(options.getOrDefault<ParserOptions>()), vectorBuilder(getDiagnostics()) {
}

CompilationUnitSyntax& Parser::parseCompilationUnit() {
    try {
        auto members = parseMemberList<MemberSyntax>(TokenKind::EndOfFile, eofToken,
                                                     [this]() { return parseMember(); });
        return factory.compilationUnit(members, eofToken);
    }
    catch (const RecursionException&) {
        return factory.compilationUnit(nullptr, eofToken);
    }
}

SyntaxNode& Parser::parseGuess() {
    // First try to parse as some kind of declaration.
    auto attributes = parseAttributes();
    if (isHierarchyInstantiation())
        return parseHierarchyInstantiation(attributes);
    if (isNetDeclaration())
        return parseNetDeclaration(attributes);
    if (isVariableDeclaration())
        return parseVariableDeclaration(attributes);

    ASSERT(attributes.empty());

    // Try to parse as an expression if possible.
    if (isPossibleExpression(peek().kind)) {
        auto& expr = parseExpression();
        if (peek(TokenKind::Semicolon))
            consume();

        return expr;
    }

    // Now try to parse as a statement.
    auto& diagnostics = getDiagnostics();
    auto& statement = parseStatement(/* allowEmpty */ true);

    // It might not have been a statement at all, in which case try a whole compilation unit
    if (statement.kind == SyntaxKind::EmptyStatement && !diagnostics.empty() &&
        diagnostics.back().code == diag::ExpectedStatement) {

        diagnostics.pop();
        auto& unit = parseCompilationUnit();

        // If there's only one member, pull it out for convenience
        if (unit.members.size() == 1)
            return *unit.members[0];
        else
            return unit;
    }

    return statement;
}

bool Parser::isDone() {
    return getLastConsumed().kind == TokenKind::EndOfFile || peek(TokenKind::EndOfFile);
}

Token Parser::getEOFToken() {
    if (eofToken.kind == TokenKind::EndOfFile)
        return eofToken;

    if (peek(TokenKind::EndOfFile))
        return consume();

    return Token();
}

ModuleDeclarationSyntax& Parser::parseModule() {
    return parseModule(parseAttributes());
}

ModuleDeclarationSyntax& Parser::parseModule(span<AttributeInstanceSyntax*> attributes) {
    auto& header = parseModuleHeader();
    auto endKind = getModuleEndKind(header.moduleKeyword.kind);

    NodeMetadata meta{ getPP().getDefaultNetType(), getPP().getTimeScale() };

    Token endmodule;
    auto members =
        parseMemberList<MemberSyntax>(endKind, endmodule, [this]() { return parseMember(); });

    auto endName = parseNamedBlockClause();
    checkBlockNames(header.name, endName);

    auto& result = factory.moduleDeclaration(getModuleDeclarationKind(header.moduleKeyword.kind),
                                             attributes, header, members, endmodule, endName);

    metadataMap[&result] = meta;
    return result;
}

ClassDeclarationSyntax& Parser::parseClass() {
    auto attributes = parseAttributes();

    Token virtualOrInterface;
    if (peek(TokenKind::VirtualKeyword) || peek(TokenKind::InterfaceKeyword))
        virtualOrInterface = consume();

    return parseClassDeclaration(attributes, virtualOrInterface);
}

Token Parser::parseLifetime() {
    auto kind = peek().kind;
    if (kind == TokenKind::StaticKeyword || kind == TokenKind::AutomaticKeyword)
        return consume();
    return Token();
}

AnsiPortListSyntax& Parser::parseAnsiPortList(Token openParen) {
    Token closeParen;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseList<isPossibleAnsiPort, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
        diag::ExpectedAnsiPort, [this] { return &parseAnsiPort(); });
    return factory.ansiPortList(openParen, buffer.copy(alloc), closeParen);
}

ModuleHeaderSyntax& Parser::parseModuleHeader() {
    auto moduleKeyword = consume();
    auto lifetime = parseLifetime();
    auto name = expect(TokenKind::Identifier);
    auto imports = parsePackageImports();
    auto parameterList = parseParameterPortList();

    PortListSyntax* ports = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        auto openParen = consume();
        if (peek(TokenKind::DotStar)) {
            auto dotStar = consume();
            ports =
                &factory.wildcardPortList(openParen, dotStar, expect(TokenKind::CloseParenthesis));
        }
        else if (isNonAnsiPort()) {
            Token closeParen;
            SmallVectorSized<TokenOrSyntax, 8> buffer;
            parseList<isPossibleNonAnsiPort, isEndOfParenList>(
                buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen,
                RequireItems::True, diag::ExpectedNonAnsiPort,
                [this] { return &parseNonAnsiPort(); }, AllowEmpty::True);
            ports = &factory.nonAnsiPortList(openParen, buffer.copy(alloc), closeParen);
        }
        else {
            ports = &parseAnsiPortList(openParen);
        }
    }

    auto semi = expect(TokenKind::Semicolon);
    return factory.moduleHeader(getModuleHeaderKind(moduleKeyword.kind), moduleKeyword, lifetime,
                                name, imports, parameterList, ports, semi);
}

ParameterPortListSyntax* Parser::parseParameterPortList() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();

    Token openParen;
    Token closeParen;
    span<TokenOrSyntax> parameters;
    parseList<isPossibleParameter, isEndOfParameterList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen,
        parameters, closeParen, RequireItems::False, diag::ExpectedParameterPort,
        [this] { return &parseParameterPort(); });

    return &factory.parameterPortList(hash, openParen, parameters, closeParen);
}

PortReferenceSyntax& Parser::parsePortReference() {
    auto name = expect(TokenKind::Identifier);

    ElementSelectSyntax* select = nullptr;
    if (peek(TokenKind::OpenBracket))
        select = &parseElementSelect();

    return factory.portReference(name, select);
}

PortExpressionSyntax& Parser::parsePortExpression() {
    if (peek(TokenKind::OpenBrace)) {
        Token openBrace, closeBrace;
        span<TokenOrSyntax> items;

        parseList<isIdentifierOrComma, isEndOfBracedList>(
            TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBrace, items,
            closeBrace, RequireItems::True, diag::ExpectedExpression,
            [this] { return &parsePortReference(); });

        return factory.portConcatenation(openBrace, items, closeBrace);
    }
    return parsePortReference();
}

NonAnsiPortSyntax& Parser::parseNonAnsiPort() {
    if (peek(TokenKind::Comma) || peek(TokenKind::CloseParenthesis))
        return factory.implicitNonAnsiPort(nullptr);

    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto openParen = expect(TokenKind::OpenParenthesis);

        PortExpressionSyntax* expr = nullptr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = &parsePortExpression();

        return factory.explicitNonAnsiPort(dot, name, openParen, expr,
                                           expect(TokenKind::CloseParenthesis));
    }

    return factory.implicitNonAnsiPort(&parsePortExpression());
}

PortHeaderSyntax& Parser::parsePortHeader(Token direction) {
    auto kind = peek().kind;
    if (isNetType(kind)) {
        auto netType = consume();
        return factory.netPortHeader(direction, netType, parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::InterfaceKeyword) {
        if (direction)
            addDiag(diag::DirectionOnInterfacePort, direction.location());

        auto keyword = consume();
        return factory.interfacePortHeader(keyword, parseDotMemberClause());
    }

    if (kind == TokenKind::InterconnectKeyword) {
        auto keyword = consume();
        auto signing = parseSigning();
        auto dimensions = parseDimensionList();
        auto& type = factory.implicitType(signing, dimensions);
        return factory.interconnectPortHeader(direction, keyword, type);
    }

    if (kind == TokenKind::VarKeyword) {
        auto varKeyword = consume();
        return factory.variablePortHeader(direction, varKeyword,
                                          parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::Identifier) {
        // could be a bunch of different things here; scan ahead to see
        if (peek(1).kind == TokenKind::Dot && peek(2).kind == TokenKind::Identifier &&
            peek(3).kind == TokenKind::Identifier) {
            auto name = consume();
            return factory.interfacePortHeader(name, parseDotMemberClause());
        }

        DataTypeSyntax* type;
        if (!isPlainPortName())
            type = &parseDataType(/* allowImplicit */ false);
        else
            type = &factory.implicitType(Token(), nullptr);

        return factory.variablePortHeader(direction, Token(), *type);
    }

    // assume we have some kind of data type here
    return factory.variablePortHeader(direction, Token(), parseDataType(/* allowImplicit */ true));
}

MemberSyntax& Parser::parseAnsiPort() {
    auto attributes = parseAttributes();
    auto kind = peek().kind;

    Token direction;
    if (isPortDirection(kind)) {
        direction = consume();
        kind = peek().kind;
    }

    if (kind == TokenKind::Dot) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto openParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr = nullptr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = &parseExpression();

        return factory.explicitAnsiPort(attributes, direction, dot, name, openParen, expr,
                                        expect(TokenKind::CloseParenthesis));
    }

    auto& header = parsePortHeader(direction);
    auto& declarator = parseDeclarator();
    return factory.implicitAnsiPort(attributes, header, declarator);
}

PortDeclarationSyntax& Parser::parsePortDeclaration(span<AttributeInstanceSyntax*> attributes) {
    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    auto& header = parsePortHeader(direction);

    Token semi;
    auto declarators = parseDeclarators(semi);
    return factory.portDeclaration(attributes, header, declarators, semi);
}

bool Parser::isPlainPortName() {
    uint32_t index = 1;
    while (peek(index).kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInPortReference>(index, TokenKind::OpenBracket,
                                                TokenKind::CloseBracket))
            return true; // if we see nonsense, we'll recover by pretending this is a plain port
    }

    auto kind = peek(index).kind;
    switch (kind) {
        case TokenKind::Equals:
        case TokenKind::Comma:
        case TokenKind::CloseParenthesis:
        case TokenKind::Semicolon:
            return true;
        default:
            return false;
    }
}

bool Parser::isNonAnsiPort() {
    auto kind = peek().kind;
    if (kind == TokenKind::Dot || kind == TokenKind::OpenBrace)
        return true;

    if (kind != TokenKind::Identifier)
        return false;

    // this might be a port name or the start of a data type
    // scan over a potential select expressions to find out
    uint32_t index = 1;
    kind = peek(index++).kind;
    if (kind == TokenKind::OpenBracket) {
        if (!scanTypePart<isNotInPortReference>(index, TokenKind::OpenBracket,
                                                TokenKind::CloseBracket))
            return false;

        kind = peek(index).kind;
    }

    // found the end; comma or close paren means this is a non-ansi port
    return kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis;
}

MemberSyntax* Parser::parseMember() {
    auto attributes = parseAttributes();

    if (isHierarchyInstantiation())
        return &parseHierarchyInstantiation(attributes);
    if (isPortDeclaration())
        return &parsePortDeclaration(attributes);
    if (isNetDeclaration())
        return &parseNetDeclaration(attributes);
    if (isVariableDeclaration())
        return &parseVariableDeclaration(attributes);

    switch (peek().kind) {
        case TokenKind::GenerateKeyword: {
            errorIfAttributes(attributes);
            auto keyword = consume();

            Token endgenerate;
            auto members = parseMemberList<MemberSyntax>(TokenKind::EndGenerateKeyword, endgenerate,
                                                         [this]() { return parseMember(); });
            return &factory.generateRegion(attributes, keyword, members, endgenerate);
        }
        case TokenKind::BeginKeyword:
            errorIfAttributes(attributes);

            // It's definitely not legal to have a generate block here on its own
            // (without an if or for loop) but some simulators seems to accept it
            // and I've found code in the wild that depends on it. We'll parse it
            // here and then issue a diagnostic about how it's not kosher.
            addDiag(diag::NonStandardGenBlock, peek().location());
            return &parseGenerateBlock();
        case TokenKind::TimeUnitKeyword:
        case TokenKind::TimePrecisionKeyword:
            errorIfAttributes(attributes);
            return &parseTimeUnitsDeclaration(attributes);
        case TokenKind::ModuleKeyword:
        case TokenKind::MacromoduleKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::PackageKeyword:
            // modules, interfaces, and programs share the same syntax
            return &parseModule(attributes);
        case TokenKind::InterfaceKeyword:
            // an interface class is different from an interface
            if (peek(1).kind == TokenKind::ClassKeyword)
                return &parseClassDeclaration(attributes, consume());
            else
                return &parseModule(attributes);
        case TokenKind::ModPortKeyword:
            return &parseModportDeclaration(attributes);
        case TokenKind::SpecParamKeyword:
        case TokenKind::BindKeyword:
        case TokenKind::AliasKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::SpecifyKeyword:
            // TODO: parse these
            break;
        case TokenKind::Identifier: {
            // Declarations and instantiations have already been handled, so if we reach this point
            // we either have a labeled assertion, or this is some kind of error.
            if (peek(1).kind == TokenKind::Colon) {
                TokenKind next = peek(2).kind;
                if (next == TokenKind::AssertKeyword || next == TokenKind::AssumeKeyword ||
                    next == TokenKind::CoverKeyword) {

                    auto name = consume();
                    auto& label = factory.namedLabel(name, expect(TokenKind::Colon));
                    auto& statement = parseAssertionStatement(&label, {});
                    switch (statement.kind) {
                        case SyntaxKind::ImmediateAssertStatement:
                        case SyntaxKind::ImmediateAssumeStatement:
                        case SyntaxKind::ImmediateCoverStatement:
                            return &factory.immediateAssertionMember(
                                attributes, statement.as<ImmediateAssertionStatementSyntax>());
                        default:
                            return &factory.concurrentAssertionMember(
                                attributes, statement.as<ConcurrentAssertionStatementSyntax>());
                    }
                }
            }
            break;
        }
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword:
        case TokenKind::RestrictKeyword: {
            auto& statement = parseAssertionStatement(nullptr, {});
            switch (statement.kind) {
                case SyntaxKind::ImmediateAssertStatement:
                case SyntaxKind::ImmediateAssumeStatement:
                case SyntaxKind::ImmediateCoverStatement:
                    return &factory.immediateAssertionMember(
                        attributes, statement.as<ImmediateAssertionStatementSyntax>());
                default:
                    return &factory.concurrentAssertionMember(
                        attributes, statement.as<ConcurrentAssertionStatementSyntax>());
            }
        }
        case TokenKind::AssignKeyword:
            return &parseContinuousAssign(attributes);
        case TokenKind::InitialKeyword: {
            auto keyword = consume();
            return &factory.proceduralBlock(getProceduralBlockKind(keyword.kind), attributes,
                                            keyword, parseStatement());
        }
        case TokenKind::FinalKeyword:
        case TokenKind::AlwaysKeyword:
        case TokenKind::AlwaysCombKeyword:
        case TokenKind::AlwaysFFKeyword:
        case TokenKind::AlwaysLatchKeyword: {
            auto keyword = consume();
            return &factory.proceduralBlock(getProceduralBlockKind(keyword.kind), attributes,
                                            keyword, parseStatement(false));
        }
        case TokenKind::ForKeyword:
            return &parseLoopGenerateConstruct(attributes);
        case TokenKind::IfKeyword:
            return &parseIfGenerateConstruct(attributes);
        case TokenKind::CaseKeyword:
            return &parseCaseGenerateConstruct(attributes);
        case TokenKind::GenVarKeyword:
            return &parseGenvarDeclaration(attributes);
        case TokenKind::TaskKeyword:
            return &parseFunctionDeclaration(attributes, SyntaxKind::TaskDeclaration,
                                             TokenKind::EndTaskKeyword);
        case TokenKind::FunctionKeyword:
            return &parseFunctionDeclaration(attributes, SyntaxKind::FunctionDeclaration,
                                             TokenKind::EndFunctionKeyword);
        case TokenKind::CoverGroupKeyword:
            return &parseCovergroupDeclaration(attributes);
        case TokenKind::ClassKeyword:
            return &parseClassDeclaration(attributes, Token());
        case TokenKind::VirtualKeyword:
            return &parseClassDeclaration(attributes, consume());
        case TokenKind::DefParamKeyword:
            return &parseDefParam(attributes);
        case TokenKind::ImportKeyword:
            if (peek(1).kind == TokenKind::StringLiteral) {
                return &parseDPIImportExport(attributes);
            }
            return &parseImportDeclaration(attributes);
        case TokenKind::ExportKeyword:
            return &parseDPIImportExport(attributes);
        case TokenKind::Semicolon:
            return &factory.emptyMember(attributes, nullptr, consume());
        case TokenKind::PropertyKeyword:
            return &parsePropertyDeclaration(attributes);
        case TokenKind::SequenceKeyword:
            return &parseSequenceDeclaration(attributes);
        case TokenKind::GlobalKeyword:
        case TokenKind::DefaultKeyword:
            if (peek(1).kind == TokenKind::ClockingKeyword) {
                return &parseClockingDeclaration(attributes);
            }
            break;
        case TokenKind::ClockingKeyword:
            return &parseClockingDeclaration(attributes);
        default:
            break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(
            attributes, nullptr,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    // otherwise, we got nothing and should just return null so that our caller will skip and try
    // again.
    return nullptr;
}

template<typename TMember, typename TParseFunc>
span<TMember*> Parser::parseMemberList(TokenKind endKind, Token& endToken, TParseFunc&& parseFunc) {
    SmallVectorSized<TMember*, 16> members;
    bool error = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || kind == endKind)
            break;

        auto member = parseFunc();
        if (!member) {
            // couldn't parse anything, skip a token and try again
            skipToken(error ? std::nullopt : std::make_optional(diag::ExpectedMember));
            error = true;
        }
        else {
            members.append(member);
            error = false;
        }
    }

    endToken = expect(endKind);
    return members.copy(alloc);
}

TimeUnitsDeclarationSyntax& Parser::parseTimeUnitsDeclaration(
    span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto time = expect(TokenKind::TimeLiteral);

    DividerClauseSyntax* divider = nullptr;
    if (keyword.kind == TokenKind::TimeUnitKeyword && peek(TokenKind::Slash)) {
        auto divide = consume();
        divider = &factory.dividerClause(divide, expect(TokenKind::TimeLiteral));
    }

    return factory.timeUnitsDeclaration(attributes, keyword, time, divider,
                                        expect(TokenKind::Semicolon));
}

MemberSyntax& Parser::parseModportSubroutinePortList(span<AttributeInstanceSyntax*> attributes) {
    auto importExport = consume();

    SmallVectorSized<TokenOrSyntax, 8> buffer;
    while (true) {
        if (peek(TokenKind::FunctionKeyword) || peek(TokenKind::TaskKeyword)) {
            auto& proto = parseFunctionPrototype();
            buffer.append(&factory.modportSubroutinePort(proto));
        }
        else {
            auto name = expect(TokenKind::Identifier);
            buffer.append(&factory.modportNamedPort(name));
            if (name.isMissing())
                break;
        }

        if (!peek(TokenKind::Comma) ||
            (peek(1).kind != TokenKind::FunctionKeyword && peek(1).kind != TokenKind::TaskKeyword &&
             peek(1).kind != TokenKind::Identifier)) {
            break;
        }

        buffer.append(consume());
    }

    return factory.modportSubroutinePortList(attributes, importExport, buffer.copy(alloc));
}

MemberSyntax& Parser::parseModportPort() {
    auto attributes = parseAttributes();

    Token direction;
    switch (peek().kind) {
        case TokenKind::ClockingKeyword: {
            auto clocking = consume();
            return factory.modportClockingPort(attributes, clocking, expect(TokenKind::Identifier));
        }
        case TokenKind::ImportKeyword:
        case TokenKind::ExportKeyword:
            return parseModportSubroutinePortList(attributes);
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::RefKeyword:
            direction = consume();
            break;
        default:
            addDiag(diag::MissingModportPortDirection, peek().location());
            direction = missingToken(TokenKind::InputKeyword, peek().location());
            break;
    }

    SmallVectorSized<TokenOrSyntax, 8> buffer;
    while (true) {
        if (peek(TokenKind::Dot)) {
            auto dot = consume();
            auto name = expect(TokenKind::Identifier);
            auto openParen = expect(TokenKind::OpenParenthesis);

            ExpressionSyntax* expr = nullptr;
            if (!peek(TokenKind::CloseParenthesis))
                expr = &parsePrimaryExpression();

            buffer.append(&factory.modportExplicitPort(dot, name, openParen, expr,
                                                       expect(TokenKind::CloseParenthesis)));
        }
        else {
            auto name = expect(TokenKind::Identifier);
            buffer.append(&factory.modportNamedPort(name));
            if (name.isMissing())
                break;
        }

        if (!peek(TokenKind::Comma) ||
            (peek(1).kind != TokenKind::Dot && peek(1).kind != TokenKind::Identifier)) {
            break;
        }

        buffer.append(consume());
    }

    return factory.modportSimplePortList(attributes, direction, buffer.copy(alloc));
}

ModportItemSyntax& Parser::parseModportItem() {
    auto name = expect(TokenKind::Identifier);

    Token openParen, closeParen;
    span<TokenOrSyntax> items;
    parseList<isPossibleModportPort, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, items,
        closeParen, RequireItems::True, diag::ExpectedModportPort,
        [this] { return &parseModportPort(); });

    auto& ports = factory.ansiPortList(openParen, items, closeParen);
    return factory.modportItem(name, ports);
}

ModportDeclarationSyntax& Parser::parseModportDeclaration(
    span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseList<isIdentifierOrComma, isSemicolon>(buffer, TokenKind::Semicolon, TokenKind::Comma,
                                                semi, RequireItems::True, diag::ExpectedIdentifier,
                                                [this] { return &parseModportItem(); });

    return factory.modportDeclaration(attributes, keyword, buffer.copy(alloc), semi);
}

FunctionPortSyntax& Parser::parseFunctionPort() {
    auto attributes = parseAttributes();
    auto constKeyword = consumeIf(TokenKind::ConstKeyword);

    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    if (constKeyword && direction.kind != TokenKind::RefKeyword) {
        auto location = direction ? direction.location() : constKeyword.location();
        addDiag(diag::ConstFunctionPortRequiresRef, location);
    }

    Token varKeyword = consumeIf(TokenKind::VarKeyword);

    // The data type is fully optional; if we see an identifier here we need
    // to disambiguate. Otherwise see if we have a port name or nothing at all.
    DataTypeSyntax* dataType = nullptr;
    if (!peek(TokenKind::Identifier))
        dataType = &parseDataType(/* allowImplicit */ true);
    else if (!isPlainPortName())
        dataType = &parseDataType(/* allowImplicit */ false);

    return factory.functionPort(attributes, constKeyword, direction, varKeyword, dataType,
                                parseDeclarator());
}

FunctionPrototypeSyntax& Parser::parseFunctionPrototype(bool allowTasks) {
    Token keyword;
    if (allowTasks && peek(TokenKind::TaskKeyword))
        keyword = consume();
    else
        keyword = expect(TokenKind::FunctionKeyword);

    auto lifetime = parseLifetime();

    // check for a return type here
    DataTypeSyntax* returnType = nullptr;
    uint32_t index = 0;
    if (!scanQualifiedName(index))
        returnType = &parseDataType(/* allowImplicit */ true);
    else {
        auto next = peek(index);
        if (next.kind != TokenKind::Semicolon && next.kind != TokenKind::OpenParenthesis)
            returnType = &parseDataType(/* allowImplicit */ true);
    }

    auto& name = parseName();

    FunctionPortListSyntax* portList = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        auto openParen = consume();
        Token closeParen;
        SmallVectorSized<TokenOrSyntax, 8> buffer;
        parseList<isPossibleFunctionPort, isEndOfParenList>(
            buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
            diag::ExpectedFunctionPort, [this] { return &parseFunctionPort(); });

        portList = &factory.functionPortList(openParen, buffer.copy(alloc), closeParen);
    }

    return factory.functionPrototype(keyword, lifetime, returnType, name, portList);
}

FunctionDeclarationSyntax& Parser::parseFunctionDeclaration(
    span<AttributeInstanceSyntax*> attributes, SyntaxKind functionKind, TokenKind endKind) {
    Token end;
    auto& prototype = parseFunctionPrototype();
    auto semi = expect(TokenKind::Semicolon);
    auto items = parseBlockItems(endKind, end);
    auto endBlockName = parseNamedBlockClause();

    Token nameToken = prototype.name->getLastToken();
    if (nameToken.kind == TokenKind::Identifier)
        checkBlockNames(nameToken, endBlockName);

    return factory.functionDeclaration(functionKind, attributes, prototype, semi, items, end,
                                       endBlockName);
}

GenvarDeclarationSyntax& Parser::parseGenvarDeclaration(span<AttributeInstanceSyntax*> attributes) {
    Token keyword;
    Token semi;
    span<TokenOrSyntax> identifiers;

    parseList<isIdentifierOrComma, isSemicolon>(
        TokenKind::GenVarKeyword, TokenKind::Semicolon, TokenKind::Comma, keyword, identifiers,
        semi, RequireItems::True, diag::ExpectedIdentifier,
        [this] { return &factory.identifierName(consume()); });

    return factory.genvarDeclaration(attributes, keyword, identifiers, semi);
}

LoopGenerateSyntax& Parser::parseLoopGenerateConstruct(span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto genvar = consumeIf(TokenKind::GenVarKeyword);
    auto identifier = expect(TokenKind::Identifier);
    auto equals = expect(TokenKind::Equals);
    auto& initialExpr = parseExpression();
    auto semi1 = expect(TokenKind::Semicolon);
    auto& stopExpr = parseExpression();
    auto semi2 = expect(TokenKind::Semicolon);
    ExpressionSyntax* iterationExpr = &parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    // Make sure that the iteration statement is one of the few allowed by the standard:
    //      genvar_identifier assignment_operator genvar_expression
    // |    inc_or_dec_operator genvar_identifier
    // |    genvar_identifier inc_or_dec_operator

    ExpressionSyntax* iterVarCheck = nullptr;
    switch (iterationExpr->kind) {
        case SyntaxKind::AssignmentExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
        case SyntaxKind::DivideAssignmentExpression:
        case SyntaxKind::ModAssignmentExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            iterVarCheck = iterationExpr->as<BinaryExpressionSyntax>().left;
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            iterVarCheck = iterationExpr->as<PrefixUnaryExpressionSyntax>().operand;
            break;
        case SyntaxKind::PostincrementExpression:
        case SyntaxKind::PostdecrementExpression:
            iterVarCheck = iterationExpr->as<PostfixUnaryExpressionSyntax>().operand;
            break;
        default:
            addDiag(diag::InvalidGenvarIterExpression, iterationExpr->getFirstToken().location())
                << iterationExpr->sourceRange();
            iterationExpr = &factory.badExpression(*iterationExpr);
            break;
    }

    // Make sure the iteration expression only mentions the genvar on the lhs.
    if (iterVarCheck && !identifier.isMissing() &&
        (iterVarCheck->kind != SyntaxKind::IdentifierName ||
         iterVarCheck->as<IdentifierNameSyntax>().identifier.valueText() !=
             identifier.valueText())) {

        addDiag(diag::ExpectedGenvarIterVar, iterVarCheck->getFirstToken().location())
            << iterVarCheck->sourceRange();
        iterationExpr = &factory.badExpression(*iterationExpr);
    }

    return factory.loopGenerate(attributes, keyword, openParen, genvar, identifier, equals,
                                initialExpr, semi1, stopExpr, semi2, *iterationExpr, closeParen,
                                parseGenerateBlock());
}

IfGenerateSyntax& Parser::parseIfGenerateConstruct(span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& block = parseGenerateBlock();

    ElseClauseSyntax* elseClause = nullptr;
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        elseClause = &factory.elseClause(elseKeyword, parseGenerateBlock());
    }

    return factory.ifGenerate(attributes, keyword, openParen, condition, closeParen, block,
                              elseClause);
}

CaseGenerateSyntax& Parser::parseCaseGenerateConstruct(span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    SmallVectorSized<CaseItemSyntax*, 8> itemBuffer;
    SourceLocation lastDefault;
    bool errored = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::DefaultKeyword) {
            if (lastDefault && !errored) {
                auto& diag = addDiag(diag::MultipleGenerateDefaultCases, peek().location());
                diag.addNote(diag::NotePreviousDefinition, lastDefault);
                errored = true;
            }

            lastDefault = peek().location();

            auto def = consume();
            auto colon = consumeIf(TokenKind::Colon);
            itemBuffer.append(&factory.defaultCaseItem(def, colon, parseGenerateBlock()));
        }
        else if (isPossibleExpression(kind)) {
            Token colon;
            SmallVectorSized<TokenOrSyntax, 8> buffer;
            parseList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            itemBuffer.append(
                &factory.standardCaseItem(buffer.copy(alloc), colon, parseGenerateBlock()));
        }
        else {
            break;
        }
    }

    if (itemBuffer.empty())
        addDiag(diag::CaseGenerateEmpty, keyword.location());

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return factory.caseGenerate(attributes, keyword, openParen, condition, closeParen,
                                itemBuffer.copy(alloc), endcase);
}

MemberSyntax& Parser::parseGenerateBlock() {
    NamedLabelSyntax* label = nullptr;
    if (!peek(TokenKind::BeginKeyword)) {
        if (!peek(TokenKind::Identifier) || peek(1).kind != TokenKind::Colon ||
            peek(2).kind != TokenKind::BeginKeyword) {
            // This is just a single member instead of a block.
            auto member = parseMember();
            if (member)
                return *member;

            // If there was some syntax error that caused parseMember to return null, fabricate an
            // empty member here and let our caller sort it out.
            return factory.emptyMember(nullptr, nullptr,
                                       missingToken(TokenKind::Semicolon, peek().location()));
        }

        auto name = consume();
        label = &factory.namedLabel(name, consume());
    }

    auto begin = consume();
    auto beginName = parseNamedBlockClause();

    Token end;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndKeyword, end,
                                                 [this]() { return parseMember(); });

    auto endName = parseNamedBlockClause();
    checkBlockNames(beginName, endName, label);

    return factory.generateBlock(nullptr, // never any attributes
                                 label, begin, beginName, members, end, endName);
}

ImplementsClauseSyntax* Parser::parseImplementsClause(TokenKind keywordKind, Token& semi) {
    if (!peek(keywordKind)) {
        semi = expect(TokenKind::Semicolon);
        return nullptr;
    }

    auto implements = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedInterfaceClassName, [this] { return &parseName(); });

    return &factory.implementsClause(implements, buffer.copy(alloc));
}

ClassDeclarationSyntax& Parser::parseClassDeclaration(span<AttributeInstanceSyntax*> attributes,
                                                      Token virtualOrInterface) {
    auto classKeyword = consume();
    auto lifetime = parseLifetime();
    auto name = expect(TokenKind::Identifier);
    auto parameterList = parseParameterPortList();

    Token semi;
    ExtendsClauseSyntax* extendsClause = nullptr;
    ImplementsClauseSyntax* implementsClause = nullptr;

    // interface classes treat "extends" as the implements list
    if (virtualOrInterface && virtualOrInterface.kind == TokenKind::InterfaceKeyword)
        implementsClause = parseImplementsClause(TokenKind::ExtendsKeyword, semi);
    else {
        if (peek(TokenKind::ExtendsKeyword)) {
            auto extends = consume();
            auto& baseName = parseName();

            ArgumentListSyntax* arguments = nullptr;
            if (peek(TokenKind::OpenParenthesis))
                arguments = &parseArgumentList();
            extendsClause = &factory.extendsClause(extends, baseName, arguments);
        }
        implementsClause = parseImplementsClause(TokenKind::ImplementsKeyword, semi);
    }

    Token endClass;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndClassKeyword, endClass,
                                                 [this]() { return parseClassMember(); });
    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.classDeclaration(attributes, virtualOrInterface, classKeyword, lifetime, name,
                                    parameterList, extendsClause, implementsClause, semi, members,
                                    endClass, endBlockName);
}

MemberSyntax* Parser::parseClassMember() {
    auto attributes = parseAttributes();

    // virtual keyword can either be a class decl, virtual interface, or a method qualifier;
    // early out here if it's a class or interface
    if (peek(TokenKind::VirtualKeyword)) {
        switch (peek(1).kind) {
            case TokenKind::ClassKeyword:
                return &parseClassDeclaration(attributes, consume());
            case TokenKind::InterfaceKeyword:
                return &factory.classPropertyDeclaration(attributes, nullptr,
                                                         parseVariableDeclaration({}));
            default:
                break;
        }
    }

    bool isPureOrExtern = false;
    SmallVectorSized<Token, 4> qualifierBuffer;
    auto kind = peek().kind;
    while (isMemberQualifier(kind)) {
        // TODO: error on bad combination / ordering
        qualifierBuffer.append(consume());
        if (kind == TokenKind::PureKeyword || kind == TokenKind::ExternKeyword)
            isPureOrExtern = true;
        kind = peek().kind;
    }
    auto qualifiers = qualifierBuffer.copy(alloc);

    if (isVariableDeclaration()) {
        auto& decl = parseVariableDeclaration({});
        if (decl.kind == SyntaxKind::ParameterDeclarationStatement)
            errorIfAttributes(attributes);
        return &factory.classPropertyDeclaration(attributes, qualifiers, decl);
    }

    if (kind == TokenKind::TaskKeyword || kind == TokenKind::FunctionKeyword) {
        if (isPureOrExtern) {
            auto& proto = parseFunctionPrototype();
            return &factory.classMethodPrototype(attributes, qualifiers, proto,
                                                 expect(TokenKind::Semicolon));
        }
        else {
            auto declKind = kind == TokenKind::TaskKeyword ? SyntaxKind::TaskDeclaration
                                                           : SyntaxKind::FunctionDeclaration;
            auto endKind = kind == TokenKind::TaskKeyword ? TokenKind::EndTaskKeyword
                                                          : TokenKind::EndFunctionKeyword;
            return &factory.classMethodDeclaration(attributes, qualifiers,
                                                   parseFunctionDeclaration({}, declKind, endKind));
        }
    }

    if (kind == TokenKind::ConstraintKeyword)
        return &parseConstraint(attributes, qualifiers);

    // qualifiers aren't allowed past this point, so return an empty member to hold them
    if (!qualifiers.empty()) {
        addDiag(diag::UnexpectedQualifiers, qualifiers[0].location());
        return &factory.emptyMember(
            attributes, qualifiers,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    switch (kind) {
        case TokenKind::ClassKeyword:
            return &parseClassDeclaration(attributes, Token());
        case TokenKind::CoverGroupKeyword:
            return &parseCovergroupDeclaration(attributes);
        case TokenKind::Semicolon:
            errorIfAttributes(attributes);
            return &factory.emptyMember(attributes, qualifiers, consume());
        default:
            break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(
            attributes, qualifiers,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    // otherwise, we got nothing and should just return null so that our caller will skip and try
    // again.
    return nullptr;
}

ContinuousAssignSyntax& Parser::parseContinuousAssign(span<AttributeInstanceSyntax*> attributes) {
    // TODO: timing control
    auto assign = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    Token semi;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedVariableAssignment, [this] { return &parseExpression(); });

    return factory.continuousAssign(attributes, assign, buffer.copy(alloc), semi);
}

DefParamAssignmentSyntax& Parser::parseDefParamAssignment() {
    auto& name = parseName();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &factory.equalsValueClause(equals, parseMinTypMaxExpression());
    }
    return factory.defParamAssignment(name, initializer);
}

DefParamSyntax& Parser::parseDefParam(span<AttributeInstanceSyntax*> attributes) {
    auto defparam = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    Token semi;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedVariableAssignment, [this] { return &parseDefParamAssignment(); });

    return factory.defParam(attributes, defparam, buffer.copy(alloc), semi);
}

CoverageOptionSyntax* Parser::parseCoverageOption(span<AttributeInstanceSyntax*> attributes) {
    auto token = peek();
    if (token.kind == TokenKind::Identifier) {
        if (token.valueText() == "option" || token.valueText() == "type_option") {
            consume();
            auto dot = expect(TokenKind::Dot);
            auto name = expect(TokenKind::Identifier);
            auto equals = expect(TokenKind::Equals);
            auto& expr = parseExpression();
            return &factory.coverageOption(attributes, token, dot, name, equals, expr,
                                           expect(TokenKind::Semicolon));
        }
    }
    return nullptr;
}

MemberSyntax* Parser::parseCoverageMember() {
    auto attributes = parseAttributes();

    // check for coverage option
    auto option = parseCoverageOption(attributes);
    if (option)
        return option;

    auto token = peek();
    if (token.kind == TokenKind::Identifier && peek(1).kind == TokenKind::Colon) {
        auto name = consume();
        auto& label = factory.namedLabel(name, consume());
        return parseCoverpoint(attributes, nullptr, &label);
    }

    if (isPossibleDataType(token.kind)) {
        auto& type = parseDataType(/* allowImplicit */ true);
        auto name = expect(TokenKind::Identifier);
        auto& label = factory.namedLabel(name, expect(TokenKind::Colon));
        return parseCoverpoint(attributes, &type, &label);
    }

    switch (token.kind) {
        case TokenKind::CoverPointKeyword:
            return parseCoverpoint(attributes, nullptr, nullptr);
        default:
            break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(
            attributes, nullptr,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    // otherwise, we got nothing and should just return null so that our caller will skip and try
    // again.
    return nullptr;
}

CoverpointSyntax* Parser::parseCoverpoint(span<AttributeInstanceSyntax*> attributes,
                                          DataTypeSyntax* type, NamedLabelSyntax* label) {
    // if we have total junk here don't bother trying to fabricate a working tree
    if (attributes.empty() && !type && !label && !peek(TokenKind::CoverPointKeyword))
        return nullptr;

    Token keyword = expect(TokenKind::CoverPointKeyword);
    auto& expr = parseExpression();
    // TODO: handle iff clause separately?

    if (peek(TokenKind::OpenBrace)) {
        auto openBrace = consume();

        Token closeBrace;
        auto members = parseMemberList<MemberSyntax>(TokenKind::CloseBrace, closeBrace,
                                                     [this]() { return parseCoverpointMember(); });
        return &factory.coverpoint(attributes, type, label, keyword, expr, openBrace, members,
                                   closeBrace, Token());
    }

    // no brace, so this is an empty list, expect a semicolon
    return &factory.coverpoint(attributes, type, label, keyword, expr, Token(), nullptr, Token(),
                               expect(TokenKind::Semicolon));
}

WithClauseSyntax* Parser::parseWithClause() {
    if (!peek(TokenKind::WithKeyword))
        return nullptr;

    auto with = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    return &factory.withClause(with, openParen, expr, expect(TokenKind::CloseParenthesis));
}

MemberSyntax* Parser::parseCoverpointMember() {
    auto attributes = parseAttributes();

    // check for coverage option
    auto option = parseCoverageOption(attributes);
    if (option)
        return option;

    Token bins;
    Token wildcard = consumeIf(TokenKind::WildcardKeyword);
    switch (peek().kind) {
        case TokenKind::BinsKeyword:
        case TokenKind::IllegalBinsKeyword:
        case TokenKind::IgnoreBinsKeyword:
            bins = consume();
            break;
        default:
            break;
    }

    if (peek(TokenKind::Semicolon)) {
        errorIfAttributes(attributes);
        return &factory.emptyMember(attributes, nullptr, consume());
    }

    // error out if we have total junk here
    if (!wildcard && !bins && attributes.empty())
        return nullptr;

    Token name = expect(TokenKind::Identifier);

    ElementSelectSyntax* selector = nullptr;
    if (peek(TokenKind::OpenBracket))
        selector = &parseElementSelect();

    // bunch of different kinds of initializers here
    CoverageBinInitializerSyntax* initializer = nullptr;
    Token equals = expect(TokenKind::Equals);

    switch (peek().kind) {
        case TokenKind::OpenBrace: {
            auto& ranges = parseOpenRangeList();
            auto with = parseWithClause();
            initializer = &factory.rangeCoverageBinInitializer(ranges, with);
            break;
        }
        case TokenKind::DefaultKeyword: {
            auto defaultKeyword = consume();
            auto sequenceKeyword = consumeIf(TokenKind::SequenceKeyword);
            initializer = &factory.defaultCoverageBinInitializer(defaultKeyword, sequenceKeyword);
            break;
        }
        case TokenKind::OpenParenthesis:
            initializer = &parseTransListInitializer();
            break;
        default: {
            auto& expr = parseExpression();
            auto with = parseWithClause();
            initializer = &factory.expressionCoverageBinInitializer(expr, with);
            break;
        }
    }

    IffClauseSyntax* iffClause = nullptr;
    if (peek(TokenKind::IffKeyword)) {
        auto iff = consume();
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpression();
        iffClause = &factory.iffClause(iff, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return &factory.coverageBins(attributes, wildcard, bins, name, selector, equals, *initializer,
                                 iffClause, expect(TokenKind::Semicolon));
}

TransRangeSyntax& Parser::parseTransRange() {
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    while (true) {
        if (peek(TokenKind::OpenBracket))
            buffer.append(&parseElementSelect());
        else
            buffer.append(&parseExpression());

        if (!peek(TokenKind::Comma))
            break;

        buffer.append(consume());
    }

    TransRepeatRangeSyntax* repeat = nullptr;
    if (peek(TokenKind::OpenBracket)) {
        auto openBracket = consume();

        Token specifier;
        switch (peek().kind) {
            case TokenKind::Star:
            case TokenKind::MinusArrow:
            case TokenKind::Equals:
                specifier = consume();
                break;
            default:
                specifier = expect(TokenKind::Star);
                break;
        }

        SelectorSyntax* selector = parseElementSelector();
        repeat = &factory.transRepeatRange(openBracket, specifier, selector,
                                           expect(TokenKind::CloseBracket));
    }

    return factory.transRange(buffer.copy(alloc), repeat);
}

TransSetSyntax& Parser::parseTransSet() {
    Token openParen;
    Token closeParen;
    span<TokenOrSyntax> list;

    parseList<isPossibleTransSet, isEndOfTransSet>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::EqualsArrow, openParen,
        list, closeParen, RequireItems::True, diag::ExpectedExpression,
        [this] { return &parseTransRange(); });

    return factory.transSet(openParen, list, closeParen);
}

TransListCoverageBinInitializerSyntax& Parser::parseTransListInitializer() {
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    while (true) {
        buffer.append(&parseTransSet());
        if (!peek(TokenKind::Comma))
            break;

        buffer.append(consume());
    }

    return factory.transListCoverageBinInitializer(buffer.copy(alloc), parseWithClause());
}

BlockEventExpressionSyntax& Parser::parseBlockEventExpression() {
    Token keyword;
    switch (peek().kind) {
        case TokenKind::BeginKeyword:
        case TokenKind::EndKeyword:
            keyword = consume();
            break;
        default:
            keyword = expect(TokenKind::BeginKeyword);
            break;
    }

    auto& name = parseName();
    auto& left = factory.primaryBlockEventExpression(keyword, name);

    if (peek(TokenKind::OrKeyword)) {
        auto op = consume();
        auto& right = parseBlockEventExpression();
        return factory.binaryBlockEventExpression(left, op, right);
    }
    return left;
}

CovergroupDeclarationSyntax& Parser::parseCovergroupDeclaration(
    span<AttributeInstanceSyntax*> attributes) {

    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);

    AnsiPortListSyntax* portList = nullptr;
    if (peek(TokenKind::OpenParenthesis))
        portList = &parseAnsiPortList(consume());

    SyntaxNode* event = nullptr;
    switch (peek().kind) {
        case TokenKind::At: {
            auto at = consume();
            event = &factory.eventControlWithExpression(at, parseEventExpression());
            break;
        }
        case TokenKind::DoubleAt:
            event = &parseBlockEventExpression();
            break;
        case TokenKind::WithKeyword: {
            auto with = consume();
            auto function = expect(TokenKind::FunctionKeyword);

            // TODO: make sure this is "sample" (maybe in the binder?)
            auto sample = expect(TokenKind::Identifier);
            if (!sample.isMissing() && sample.valueText() != "sample"sv)
                addDiag(diag::ExpectedSampleKeyword, sample.location());

            auto& samplePortList = parseAnsiPortList(expect(TokenKind::OpenParenthesis));
            event = &factory.withFunctionSample(with, function, sample, samplePortList);
            break;
        }
        default:
            break;
    }

    auto semi = expect(TokenKind::Semicolon);

    Token endGroup;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndGroupKeyword, endGroup,
                                                 [this]() { return parseCoverageMember(); });
    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.covergroupDeclaration(attributes, keyword, name, portList, event, semi, members,
                                         endGroup, endBlockName);
}

MemberSyntax& Parser::parseConstraint(span<AttributeInstanceSyntax*> attributes,
                                      span<Token> qualifiers) {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    if (peek(TokenKind::Semicolon)) {
        // this is just a prototype
        return factory.constraintPrototype(attributes, qualifiers, keyword, name, consume());
    }
    return factory.constraintDeclaration(attributes, qualifiers, keyword, name,
                                         parseConstraintBlock());
}

ConstraintBlockSyntax& Parser::parseConstraintBlock() {
    Token closeBrace;
    auto openBrace = expect(TokenKind::OpenBrace);
    auto members = parseMemberList<ConstraintItemSyntax>(
        TokenKind::CloseBrace, closeBrace, [this]() { return parseConstraintItem(false); });
    return factory.constraintBlock(openBrace, members, closeBrace);
}

ExpressionSyntax& Parser::parseExpressionOrDist() {
    auto& expr = parseExpression();
    if (!peek(TokenKind::DistKeyword))
        return expr;

    auto& dist = parseDistConstraintList();
    return factory.expressionOrDist(expr, dist);
}

ConstraintItemSyntax* Parser::parseConstraintItem(bool allowBlock) {
    switch (peek().kind) {
        case TokenKind::SolveKeyword: {
            auto solve = consume();
            Token before;
            SmallVectorSized<TokenOrSyntax, 4> beforeBuffer;
            parseList<isPossibleExpression, isBeforeOrSemicolon>(
                beforeBuffer, TokenKind::BeforeKeyword, TokenKind::Comma, before,
                RequireItems::True, diag::ExpectedExpression,
                [this] { return &parsePrimaryExpression(); });

            Token semi;
            SmallVectorSized<TokenOrSyntax, 4> afterBuffer;
            parseList<isPossibleExpression, isSemicolon>(
                afterBuffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parsePrimaryExpression(); });

            return &factory.solveBeforeConstraint(solve, beforeBuffer.copy(alloc), before,
                                                  afterBuffer.copy(alloc), semi);
        }
        case TokenKind::DisableKeyword: {
            auto disable = consume();
            auto soft = expect(TokenKind::SoftKeyword);
            auto& name = parseName();
            return &factory.disableConstraint(disable, soft, name, expect(TokenKind::Semicolon));
        }
        case TokenKind::ForeachKeyword: {
            auto keyword = consume();
            auto& vars = parseForeachLoopVariables();
            return &factory.loopConstraint(keyword, vars, *parseConstraintItem(true));
        }
        case TokenKind::IfKeyword: {
            auto ifKeyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& constraints = *parseConstraintItem(true);

            ElseConstraintClauseSyntax* elseClause = nullptr;
            if (peek(TokenKind::ElseKeyword)) {
                auto elseKeyword = consume();
                elseClause = &factory.elseConstraintClause(elseKeyword, *parseConstraintItem(true));
            }
            return &factory.conditionalConstraint(ifKeyword, openParen, condition, closeParen,
                                                  constraints, elseClause);
        }
        case TokenKind::UniqueKeyword: {
            auto keyword = consume();
            auto& list = parseOpenRangeList();
            return &factory.uniquenessConstraint(keyword, list, expect(TokenKind::Semicolon));
        }
        case TokenKind::SoftKeyword: {
            auto soft = consume();
            auto& exprOrDist = parseExpressionOrDist();
            return &factory.expressionConstraint(soft, exprOrDist, expect(TokenKind::Semicolon));
        }
        case TokenKind::OpenBrace: {
            // Ambiguity here: an open brace could either be the start of a constraint block
            // or the start of a concatenation expression. Descend into the expression until
            // we can find out for sure one way or the other.
            if (allowBlock) {
                uint32_t index = 1;
                if (!scanTypePart<isNotInConcatenationExpr>(index, TokenKind::OpenBrace,
                                                            TokenKind::CloseBrace))
                    return &parseConstraintBlock();
            }
            break;
        }
        default:
            break;
    }

    // If we reach this point we have some invalid syntax here. If we're in a nested
    // constraint block (identified by allowBlock == true) then we should make up
    // an item and return. This is accomplished by falling through to the parseSubExpression below.
    // Otherwise, this is the top level and we should return nullptr so that we skip over
    // the offending token.
    if (!isPossibleExpression(peek().kind) && !allowBlock)
        return nullptr;

    // at this point we either have an expression with optional distribution or
    // we have an implication constraint
    auto expr = &parseSubExpression(ExpressionOptions::ConstraintContext, 0);
    if (peek(TokenKind::MinusArrow)) {
        auto arrow = consume();
        return &factory.implicationConstraint(*expr, arrow, *parseConstraintItem(true));
    }

    if (peek(TokenKind::DistKeyword)) {
        auto& dist = parseDistConstraintList();
        expr = &factory.expressionOrDist(*expr, dist);
    }

    return &factory.expressionConstraint(Token(), *expr, expect(TokenKind::Semicolon));
}

DistConstraintListSyntax& Parser::parseDistConstraintList() {
    auto dist = consume();

    Token openBrace;
    Token closeBrace;
    span<TokenOrSyntax> list;

    parseList<isPossibleOpenRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBrace, list, closeBrace,
        RequireItems::True, diag::ExpectedDistItem, [this] { return &parseDistItem(); });

    return factory.distConstraintList(dist, openBrace, list, closeBrace);
}

DistItemSyntax& Parser::parseDistItem() {
    auto& range = parseOpenRangeElement();

    DistWeightSyntax* weight = nullptr;
    if (peek(TokenKind::ColonEquals) || peek(TokenKind::ColonSlash)) {
        auto op = consume();
        weight = &factory.distWeight(op, parseExpression());
    }

    return factory.distItem(range, weight);
}

Token Parser::parseSigning() {
    switch (peek().kind) {
        case TokenKind::SignedKeyword:
        case TokenKind::UnsignedKeyword:
            return consume();
        default:
            return Token();
    }
}

VariableDimensionSyntax* Parser::parseDimension() {
    if (!peek(TokenKind::OpenBracket))
        return nullptr;

    auto openBracket = consume();

    DimensionSpecifierSyntax* specifier = nullptr;
    switch (peek().kind) {
        case TokenKind::CloseBracket:
            // empty specifier
            break;
        case TokenKind::Star:
            specifier = &factory.wildcardDimensionSpecifier(consume());
            break;
        case TokenKind::Dollar: {
            auto dollar = consume();

            ColonExpressionClauseSyntax* colonExpressionClause = nullptr;
            if (peek(TokenKind::Colon)) {
                auto colon = consume();
                colonExpressionClause = &factory.colonExpressionClause(colon, parseExpression());
            }
            specifier = &factory.queueDimensionSpecifier(dollar, colonExpressionClause);
            break;
        }
        default: {
            auto selector = parseElementSelector();
            ASSERT(selector);
            specifier = &factory.rangeDimensionSpecifier(*selector);
            break;
        }
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return &factory.variableDimension(openBracket, specifier, closeBracket);
}

span<VariableDimensionSyntax*> Parser::parseDimensionList() {
    SmallVectorSized<VariableDimensionSyntax*, 4> buffer;
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
        return &factory.dotMemberClause(dot, expect(TokenKind::Identifier));
    }
    return nullptr;
}

StructUnionTypeSyntax& Parser::parseStructUnion(SyntaxKind syntaxKind) {
    auto keyword = consume();
    auto tagged = consumeIf(TokenKind::TaggedKeyword);
    auto packed = consumeIf(TokenKind::PackedKeyword);
    auto signing = parseSigning();
    auto openBrace = expect(TokenKind::OpenBrace);

    Token closeBrace;
    SmallVectorSized<StructUnionMemberSyntax*, 8> buffer;

    if (openBrace.isMissing())
        closeBrace = missingToken(TokenKind::CloseBrace, openBrace.location());
    else {
        auto kind = peek().kind;
        while (kind != TokenKind::CloseBrace && kind != TokenKind::EndOfFile) {
            auto attributes = parseAttributes();

            Token randomQualifier;
            switch (peek().kind) {
                case TokenKind::RandKeyword:
                case TokenKind::RandCKeyword:
                    randomQualifier = consume();
                    break;
                default:
                    break;
            }

            auto& type = parseDataType(/* allowImplicit */ false);

            Token semi;
            auto declarators = parseDeclarators(semi);

            buffer.append(
                &factory.structUnionMember(attributes, randomQualifier, type, declarators, semi));
            kind = peek().kind;
        }
        closeBrace = expect(TokenKind::CloseBrace);
    }

    return factory.structUnionType(syntaxKind, keyword, tagged, packed, signing, openBrace,
                                   buffer.copy(alloc), closeBrace, parseDimensionList());
}

EnumTypeSyntax& Parser::parseEnum() {
    auto keyword = consume();

    DataTypeSyntax* baseType = nullptr;
    if (!peek(TokenKind::OpenBrace))
        baseType = &parseDataType(/* allowImplicit */ false);

    auto openBrace = expect(TokenKind::OpenBrace);

    Token closeBrace;
    span<TokenOrSyntax> declarators;
    if (openBrace.isMissing())
        closeBrace = missingToken(TokenKind::CloseBrace, openBrace.location());
    else
        declarators = parseDeclarators<isCloseBrace>(TokenKind::CloseBrace, closeBrace);

    return factory.enumType(keyword, baseType, openBrace, declarators, closeBrace,
                            parseDimensionList());
}

DataTypeSyntax& Parser::parseDataType(bool allowImplicit) {
    auto kind = peek().kind;
    auto type = getIntegerType(kind);
    if (type != SyntaxKind::Unknown) {
        auto keyword = consume();
        auto signing = parseSigning();
        return factory.integerType(type, keyword, signing, parseDimensionList());
    }

    type = getKeywordType(kind);
    if (type != SyntaxKind::Unknown)
        return factory.keywordType(type, consume());

    switch (kind) {
        case TokenKind::StructKeyword:
            return parseStructUnion(SyntaxKind::StructType);
        case TokenKind::UnionKeyword:
            return parseStructUnion(SyntaxKind::UnionType);
        case TokenKind::EnumKeyword:
            return parseEnum();
        case TokenKind::VirtualKeyword: {
            auto virtualKeyword = consume();
            auto interfaceKeyword = consumeIf(TokenKind::InterfaceKeyword);
            auto name = expect(TokenKind::Identifier);
            auto parameters = parseParameterValueAssignment();
            return factory.virtualInterfaceType(virtualKeyword, interfaceKeyword, name, parameters,
                                                parseDotMemberClause());
        }
        case TokenKind::UnitSystemName:
            return factory.namedType(parseName());
        case TokenKind::TypeKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseExpression();
            return factory.typeReference(keyword, openParen, expr,
                                         expect(TokenKind::CloseParenthesis));
        }
        default:
            break;
    }

    if (kind == TokenKind::Identifier) {
        if (!allowImplicit)
            return factory.namedType(parseName());
        else {
            // If we're allowed to have an implicit type here, it means there's a chance this
            // identifier is actually the name of something else (like a declaration) and that the
            // type should be implicit. Check if there's another identifier right after us
            // before deciding which one we're looking at.
            uint32_t index = 0;
            if (scanQualifiedName(index) && scanDimensionList(index) &&
                peek(index).kind == TokenKind::Identifier)
                return factory.namedType(parseName());
            return factory.implicitType(Token(), nullptr);
        }
    }

    auto signing = parseSigning();
    auto dimensions = parseDimensionList();

    if (!allowImplicit)
        addDiag(diag::ImplicitNotAllowed, peek().location());

    return factory.implicitType(signing, dimensions);
}

MemberSyntax& Parser::parseNetDeclaration(span<AttributeInstanceSyntax*> attributes) {
    auto netType = consume();

    NetStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        // TODO: strength specifiers
    }

    Token expansionHint;
    if (peek(TokenKind::VectoredKeyword) || peek(TokenKind::ScalaredKeyword))
        expansionHint = consume();

    auto& type = parseDataType(/* allowImplicit */ true);

    // TODO: delay control

    Token semi;
    auto declarators = parseDeclarators(semi);

    return factory.netDeclaration(attributes, netType, strength, expansionHint, type, declarators,
                                  semi);
}

MemberSyntax& Parser::parseVariableDeclaration(span<AttributeInstanceSyntax*> attributes) {
    switch (peek().kind) {
        case TokenKind::TypedefKeyword: {
            auto typedefKeyword = consume();
            switch (peek().kind) {
                case TokenKind::EnumKeyword:
                case TokenKind::StructKeyword:
                case TokenKind::UnionKeyword:
                case TokenKind::ClassKeyword:
                    if (peek(1).kind == TokenKind::Identifier &&
                        peek(2).kind == TokenKind::Semicolon) {

                        auto keyword = consume();
                        auto name = consume();
                        return factory.forwardTypedefDeclaration(attributes, typedefKeyword,
                                                                 keyword, name, consume());
                    }
                    break;
                case TokenKind::InterfaceKeyword: {
                    auto interfaceKeyword = consume();
                    auto classKeyword = expect(TokenKind::ClassKeyword);
                    auto name = expect(TokenKind::Identifier);
                    return factory.forwardInterfaceClassTypedefDeclaration(
                        attributes, typedefKeyword, interfaceKeyword, classKeyword, name,
                        expect(TokenKind::Semicolon));
                }
                case TokenKind::Identifier:
                    if (peek(1).kind == TokenKind::Semicolon) {
                        auto name = consume();
                        return factory.forwardTypedefDeclaration(attributes, typedefKeyword,
                                                                 Token(), name, consume());
                    }
                    break;
                default:
                    break;
            }
            auto& type = parseDataType(/* allowImplicit */ false);
            auto name = expect(TokenKind::Identifier);
            auto dims = parseDimensionList();
            return factory.typedefDeclaration(attributes, typedefKeyword, type, name, dims,
                                              expect(TokenKind::Semicolon));
        }
        case TokenKind::ParameterKeyword:
        case TokenKind::LocalParamKeyword: {
            Token semi;
            auto& parameter = parseParameterDecl(consume(), &semi);
            return factory.parameterDeclarationStatement(attributes, parameter, semi);
        }
        case TokenKind::LetKeyword: {
            auto let = consume();
            auto identifier = expect(TokenKind::Identifier);
            auto portList = parseAssertionItemPortList(TokenKind::LetKeyword);
            auto& initializer =
                factory.equalsValueClause(expect(TokenKind::Equals), parseExpression());
            return factory.letDeclaration(attributes, let, identifier, portList, initializer,
                                          expect(TokenKind::Semicolon));
        }
        case TokenKind::ImportKeyword:
            return parseImportDeclaration(attributes);
        case TokenKind::NetTypeKeyword:
            return parseNetTypeDecl(attributes);
        default:
            break;
    }

    bool hasVar = false;
    SmallVectorSized<Token, 4> modifiers;
    auto kind = peek().kind;
    while (isDeclarationModifier(kind)) {
        // TODO: error on bad combination / ordering
        modifiers.append(consume());
        if (kind == TokenKind::VarKeyword)
            hasVar = true;
        kind = peek().kind;
    }

    auto& dataType = parseDataType(/* allowImplicit */ hasVar);

    Token semi;
    auto declarators = parseDeclarators(semi);

    return factory.dataDeclaration(attributes, modifiers.copy(alloc), dataType, declarators, semi);
}

DeclaratorSyntax& Parser::parseDeclarator() {
    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &factory.equalsValueClause(equals, parseMinTypMaxExpression());
    }

    return factory.declarator(name, dimensions, initializer);
}

span<TokenOrSyntax> Parser::parseOneDeclarator() {
    SmallVectorSized<TokenOrSyntax, 2> buffer;
    buffer.append(&parseDeclarator());
    return buffer.copy(alloc);
}

template<bool (*IsEnd)(TokenKind)>
span<TokenOrSyntax> Parser::parseDeclarators(TokenKind endKind, Token& end) {
    SmallVectorSized<TokenOrSyntax, 4> buffer;
    parseList<isIdentifierOrComma, IsEnd>(buffer, endKind, TokenKind::Comma, end,
                                          RequireItems::True, diag::ExpectedDeclarator,
                                          [this] { return &parseDeclarator(); });

    return buffer.copy(alloc);
}

span<TokenOrSyntax> Parser::parseDeclarators(Token& semi) {
    return parseDeclarators<isSemicolon>(TokenKind::Semicolon, semi);
}

span<AttributeInstanceSyntax*> Parser::parseAttributes() {
    SmallVectorSized<AttributeInstanceSyntax*, 4> buffer;
    while (peek(TokenKind::OpenParenthesisStar)) {
        Token openParen;
        Token closeParen;
        span<TokenOrSyntax> list;

        parseList<isIdentifierOrComma, isEndOfAttribute>(
            TokenKind::OpenParenthesisStar, TokenKind::StarCloseParenthesis, TokenKind::Comma,
            openParen, list, closeParen, RequireItems::True, diag::ExpectedAttribute,
            [this] { return &parseAttributeSpec(); });

        buffer.append(&factory.attributeInstance(openParen, list, closeParen));
    }
    return buffer.copy(alloc);
}

AttributeSpecSyntax& Parser::parseAttributeSpec() {
    auto name = expect(TokenKind::Identifier);

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &factory.equalsValueClause(equals, parseExpression());
    }

    return factory.attributeSpec(name, initializer);
}

span<PackageImportDeclarationSyntax*> Parser::parsePackageImports() {
    SmallVectorSized<PackageImportDeclarationSyntax*, 4> buffer;
    while (peek(TokenKind::ImportKeyword))
        buffer.append(&parseImportDeclaration({}));
    return buffer.copy(alloc);
}

PackageImportDeclarationSyntax& Parser::parseImportDeclaration(
    span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 4> items;
    parseList<isIdentifierOrComma, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                                RequireItems::True, diag::ExpectedPackageImport,
                                                [this] { return &parsePackageImportItem(); });

    return factory.packageImportDeclaration(attributes, keyword, items.copy(alloc), semi);
}

PackageImportItemSyntax& Parser::parsePackageImportItem() {
    auto package = expect(TokenKind::Identifier);
    auto doubleColon = expect(TokenKind::DoubleColon);

    Token item;
    if (peek(TokenKind::Star))
        item = consume();
    else
        item = expect(TokenKind::Identifier);

    return factory.packageImportItem(package, doubleColon, item);
}

NetTypeDeclarationSyntax& Parser::parseNetTypeDecl(span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto& type = parseDataType(false);
    auto name = expect(TokenKind::Identifier);

    WithFunctionClauseSyntax* withFunction = nullptr;
    if (peek(TokenKind::WithKeyword)) {
        auto with = consume();
        withFunction = &factory.withFunctionClause(with, parseName());
    }

    return factory.netTypeDeclaration(attributes, keyword, type, name, withFunction,
                                      expect(TokenKind::Semicolon));
}

DPIImportExportSyntax& Parser::parseDPIImportExport(span<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto stringLiteral = expect(TokenKind::StringLiteral);
    if (!stringLiteral.isMissing() && stringLiteral.valueText() != "DPI-C" &&
        stringLiteral.valueText() != "DPI") {
        addDiag(diag::ExpectedDPISpecString, stringLiteral.location());
    }

    Token property, name, equals;
    if (keyword.kind == TokenKind::ImportKeyword &&
        (peek(TokenKind::ContextKeyword) || peek(TokenKind::PureKeyword))) {
        property = consume();
    }

    if (peek(TokenKind::Identifier)) {
        name = consume();
        equals = expect(TokenKind::Equals);
    }

    auto& method = parseFunctionPrototype(property.kind != TokenKind::PureKeyword);
    auto semi = expect(TokenKind::Semicolon);
    return factory.dPIImportExport(attributes, keyword, stringLiteral, property, name, equals,
                                   method, semi);
}

AssertionItemPortListSyntax* Parser::parseAssertionItemPortList(TokenKind declarationKind) {
    if (!peek(TokenKind::OpenParenthesis) ||
        (declarationKind != TokenKind::PropertyKeyword &&
         declarationKind != TokenKind::SequenceKeyword && declarationKind != TokenKind::LetKeyword))
        return nullptr;

    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 4> buffer;
    Token closeParen;

    parseList<isPossiblePropertyPortItem, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::True,
        diag::ExpectedAssertionItemPort, [this, declarationKind] {
            auto attributes = parseAttributes();
            Token local;
            Token direction;
            if (declarationKind == TokenKind::PropertyKeyword ||
                declarationKind == TokenKind::SequenceKeyword) {
                local = consumeIf(TokenKind::LocalKeyword);
                if (local &&
                    (peek(TokenKind::InputKeyword) ||
                     (declarationKind == TokenKind::SequenceKeyword &&
                      (peek(TokenKind::OutputKeyword) || peek(TokenKind::InOutKeyword))))) {
                    direction = consume();
                }
            }

            DataTypeSyntax* type;
            switch (peek().kind) {
                case TokenKind::PropertyKeyword:
                    if (declarationKind != TokenKind::PropertyKeyword) {
                        type = &parseDataType(true);
                        break;
                    }
                    type = &factory.keywordType(SyntaxKind::PropertyType, consume());
                    break;
                case TokenKind::SequenceKeyword:
                    if (declarationKind == TokenKind::LetKeyword) {
                        type = &parseDataType(true);
                        break;
                    }
                    type = &factory.keywordType(SyntaxKind::SequenceType, consume());
                    break;
                case TokenKind::UntypedKeyword:
                    type = &factory.keywordType(SyntaxKind::Untyped, consume());
                    break;
                default:
                    type = &parseDataType(true);
                    break;
            }
            ASSERT(type);

            auto& declarator = parseDeclarator();
            return &factory.assertionItemPort(attributes, local, direction, *type, declarator);
        });

    return &factory.assertionItemPortList(openParen, buffer.copy(alloc), closeParen);
}

PropertyDeclarationSyntax& Parser::parsePropertyDeclaration(
    span<AttributeInstanceSyntax*> attributes) {

    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    auto portList = parseAssertionItemPortList(keyword.kind);
    auto semi = expect(TokenKind::Semicolon);

    SmallVectorSized<MemberSyntax*, 4> declarations;
    while (isVariableDeclaration())
        declarations.append(&parseVariableDeclaration({}));

    auto& spec = parsePropertySpec();
    Token optSemi = consumeIf(TokenKind::Semicolon);
    Token end = expect(TokenKind::EndPropertyKeyword);

    auto blockName = parseNamedBlockClause();
    checkBlockNames(name, blockName);

    return factory.propertyDeclaration(attributes, keyword, name, portList, semi,
                                       declarations.copy(alloc), spec, optSemi, end, blockName);
}

SequenceDeclarationSyntax& Parser::parseSequenceDeclaration(
    span<AttributeInstanceSyntax*> attributes) {

    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    auto portList = parseAssertionItemPortList(keyword.kind);
    auto semi = expect(TokenKind::Semicolon);

    SmallVectorSized<MemberSyntax*, 4> declarations;
    while (isVariableDeclaration())
        declarations.append(&parseVariableDeclaration({}));

    // TODO: Parse all sequence expressions
    auto& expr = parseExpression();
    Token semi2 = expect(TokenKind::Semicolon);
    Token end = expect(TokenKind::EndSequenceKeyword);

    auto blockName = parseNamedBlockClause();
    checkBlockNames(name, blockName);

    return factory.sequenceDeclaration(attributes, keyword, name, portList, semi,
                                       declarations.copy(alloc), expr, semi2, end, blockName);
}

ParameterDeclarationBaseSyntax& Parser::parseParameterPort() {
    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword))
        return parseParameterDecl(consume(), nullptr);

    // this is a normal parameter without the actual parameter keyword
    return parseParameterDecl(Token(), nullptr);
}

TypeAssignmentSyntax& Parser::parseTypeAssignment() {
    auto name = expect(TokenKind::Identifier);

    EqualsTypeClauseSyntax* assignment = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        assignment = &factory.equalsTypeClause(equals, parseDataType(/* allowImplicit */ false));
    }

    return factory.typeAssignment(name, assignment);
}

ParameterDeclarationBaseSyntax& Parser::parseParameterDecl(Token keyword, Token* semi) {
    // Check for a type parameter. We need to check for a parenthesis to see if
    // this is actually a type reference for a normal parameter.
    if (peek(TokenKind::TypeKeyword) && peek(1).kind != TokenKind::OpenParenthesis) {
        auto typeKeyword = consume();

        SmallVectorSized<TokenOrSyntax, 4> decls;
        if (semi) {
            parseList<isIdentifierOrComma, isSemicolon>(
                decls, TokenKind::Semicolon, TokenKind::Comma, *semi, RequireItems::True,
                diag::ExpectedParameterPort, [this] { return &parseTypeAssignment(); });
        }
        else {
            while (true) {
                decls.append(&parseTypeAssignment());
                if (!peek(TokenKind::Comma) || peek(1).kind != TokenKind::Identifier ||
                    (peek(2).kind != TokenKind::Equals && peek(2).kind != TokenKind::Comma)) {
                    break;
                }

                decls.append(consume());
            }
        }

        return factory.typeParameterDeclaration(keyword, typeKeyword, decls.copy(alloc));
    }
    else {
        auto& type = parseDataType(/* allowImplicit */ true);

        // If the semi pointer is given, we should parse a list of decls.
        // Otherwise we're in a parameter port list and should just parse one.
        span<TokenOrSyntax> decls;
        if (semi)
            decls = parseDeclarators(*semi);
        else
            decls = parseOneDeclarator();

        return factory.parameterDeclaration(keyword, type, decls);
    }
}

ClockingSkewSyntax* Parser::parseClockingSkew() {
    Token edge, hash;
    ExpressionSyntax* value = nullptr;
    if (peek(TokenKind::EdgeKeyword) || peek(TokenKind::PosEdgeKeyword) ||
        peek(TokenKind::NegEdgeKeyword))
        edge = consume();

    if (peek(TokenKind::Hash)) {
        hash = consume();
        value = &parsePrimaryExpression();
    }

    if (!edge && !hash)
        return nullptr;
    return &factory.clockingSkew(edge, hash, value);
}

ClockingDeclarationSyntax& Parser::parseClockingDeclaration(
    span<AttributeInstanceSyntax*> attributes) {

    Token globalOrDefault;
    if (!peek(TokenKind::ClockingKeyword))
        globalOrDefault = consume();

    Token clocking = expect(TokenKind::ClockingKeyword);
    Token blockName = expect(TokenKind::Identifier);
    Token at, eventIdentifier;
    ParenthesizedEventExpressionSyntax* event = nullptr;

    if (peek(TokenKind::At)) {
        at = consume();
        if (peek(TokenKind::OpenParenthesis)) {
            auto openParen = consume();
            auto& innerExpr = parseEventExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            event = &factory.parenthesizedEventExpression(openParen, innerExpr, closeParen);
        }
        else {
            eventIdentifier = expect(TokenKind::Identifier);
        }
    }

    Token semi = expect(TokenKind::Semicolon);
    SmallVectorSized<ClockingItemSyntax*, 4> buffer;
    SmallVectorSized<Token, 4> skipped;

    if (globalOrDefault.kind != TokenKind::GlobalKeyword) {
        bool error = false;
        while (!isEndKeyword(peek().kind) && !peek(TokenKind::EndOfFile)) {
            Token defaultKeyword, inputKeyword, outputKeyword;
            ClockingDirectionSyntax* direction = nullptr;
            ClockingSkewSyntax *inputSkew = nullptr, *outputSkew = nullptr;
            MemberSyntax* declaration = nullptr;

            switch (peek().kind) {
                case TokenKind::DefaultKeyword:
                case TokenKind::InputKeyword:
                case TokenKind::OutputKeyword:
                    defaultKeyword = consumeIf(TokenKind::DefaultKeyword);
                    if (peek(TokenKind::InputKeyword)) {
                        inputKeyword = consume();
                        inputSkew = parseClockingSkew();
                    }
                    if (peek(TokenKind::OutputKeyword)) {
                        outputKeyword = consume();
                        outputSkew = parseClockingSkew();
                    }
                    direction = &factory.clockingDirection(inputKeyword, inputSkew, outputKeyword,
                                                           outputSkew, Token());
                    break;
                case TokenKind::InOutKeyword:
                    direction =
                        &factory.clockingDirection(Token(), nullptr, Token(), nullptr, consume());
                    break;
                default:
                    declaration = parseMember();
                    break;
            }

            if (!declaration && !defaultKeyword && !direction) {
                auto token = consume();
                skipped.append(token);
                if (!error) {
                    addDiag(diag::ExpectedClockingSkew, peek().location());
                    error = true;
                }
                continue;
            }

            Token innerSemi;
            SmallVectorSized<TokenOrSyntax, 4> assignments;
            if (!declaration && !defaultKeyword) {
                parseList<isIdentifierOrComma, isSemicolon>(
                    assignments, TokenKind::Semicolon, TokenKind::Comma, innerSemi,
                    RequireItems::True, diag::ExpectedIdentifier,
                    [this] { return &parseAttributeSpec(); });
            }
            else if (!declaration) {
                innerSemi = expect(TokenKind::Semicolon);
            }

            error = false;
            buffer.append(&factory.clockingItem(defaultKeyword, direction, assignments.copy(alloc),
                                                innerSemi, declaration));
        }
    }

    Token endClocking = expect(TokenKind::EndClockingKeyword);
    NamedBlockClauseSyntax* endBlockName = parseNamedBlockClause();
    checkBlockNames(blockName, endBlockName);

    return factory.clockingDeclaration(attributes, globalOrDefault, clocking, blockName, at, event,
                                       eventIdentifier, semi, buffer.copy(alloc), endClocking,
                                       endBlockName);
}

HierarchyInstantiationSyntax& Parser::parseHierarchyInstantiation(
    span<AttributeInstanceSyntax*> attributes) {

    auto type = expect(TokenKind::Identifier);
    auto parameters = parseParameterValueAssignment();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> items;
    parseList<isIdentifierOrComma, isSemicolon>(
        items, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedHierarchicalInstantiation, [this] { return &parseHierarchicalInstance(); });

    return factory.hierarchyInstantiation(attributes, type, parameters, items.copy(alloc), semi);
}

HierarchicalInstanceSyntax& Parser::parseHierarchicalInstance() {
    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    Token openParen;
    Token closeParen;
    span<TokenOrSyntax> items;

    parseList<isPossiblePortConnection, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, items,
        closeParen, RequireItems::False, diag::ExpectedPortConnection,
        [this] { return &parsePortConnection(); });

    return factory.hierarchicalInstance(name, dimensions, openParen, items, closeParen);
}

PortConnectionSyntax& Parser::parsePortConnection() {
    auto attributes = parseAttributes();

    // Allow for empty port connections.
    if (peek(TokenKind::Comma))
        return factory.orderedPortConnection(attributes, nullptr);

    if (peek(TokenKind::DotStar))
        return factory.wildcardPortConnection(attributes, consume());

    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);

        ExpressionSyntax* expr = nullptr;
        Token openParen, closeParen;

        if (peek(TokenKind::OpenParenthesis)) {
            openParen = consume();
            if (!peek(TokenKind::CloseParenthesis))
                expr = &parseExpression();

            closeParen = expect(TokenKind::CloseParenthesis);
        }
        return factory.namedPortConnection(attributes, dot, name, openParen, expr, closeParen);
    }
    return factory.orderedPortConnection(attributes, &parseExpression());
}

bool Parser::isPortDeclaration() {
    // TODO: check for interface port declaration
    return isPortDirection(peek().kind);
}

bool Parser::isNetDeclaration() {
    // TODO: other net types
    return isNetType(peek().kind);
}

bool Parser::isVariableDeclaration() {
    uint32_t index = 0;
    while (peek(index).kind == TokenKind::OpenParenthesisStar) {
        // scan over attributes
        while (true) {
            auto kind = peek(++index).kind;
            if (kind == TokenKind::EndOfFile)
                return false;
            if (kind == TokenKind::OpenParenthesisStar || kind == TokenKind::StarCloseParenthesis)
                break;
        }
    }

    // decide whether a statement is a declaration or the start of an expression
    auto kind = peek(index).kind;
    switch (kind) {
        // some tokens unambiguously start a declaration
        case TokenKind::VarKeyword:
        case TokenKind::AutomaticKeyword:
        case TokenKind::StaticKeyword:
        case TokenKind::CHandleKeyword:
        case TokenKind::EventKeyword:
        case TokenKind::StructKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::EnumKeyword:
        case TokenKind::TypedefKeyword:
        case TokenKind::NetTypeKeyword:
        case TokenKind::LocalParamKeyword:
        case TokenKind::ParameterKeyword:
        case TokenKind::LetKeyword:
        case TokenKind::ImportKeyword:
            return true;

        // this could be a virtual interface, a virtual class declaration, or a virtual function
        case TokenKind::VirtualKeyword:
            if (peek(++index).kind == TokenKind::InterfaceKeyword)
                return true;
            if (!scanQualifiedName(index))
                return false;
            if (peek(index).kind == TokenKind::Dot)
                return true;
            break;

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
            auto next = peek(++index).kind;
            return next != TokenKind::Apostrophe && next != TokenKind::ApostropheOpenBrace;
        }
        default:
            break;
    }

    if (!scanQualifiedName(index))
        return false;

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // next token is the decider; declarations must have an identifier here
    return peek(index).kind == TokenKind::Identifier;
}

bool Parser::isHierarchyInstantiation() {
    uint32_t index = 0;
    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    // skip over optional parameter value assignment
    if (peek(index).kind == TokenKind::Hash) {
        if (peek(++index).kind != TokenKind::OpenParenthesis)
            return false;
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                       TokenKind::CloseParenthesis))
            return false;
    }

    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // a parenthesis here means we're definitely doing an instantiation
    return peek(index).kind == TokenKind::OpenParenthesis;
}

bool Parser::scanDimensionList(uint32_t& index) {
    while (peek(index).kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return false;
    }
    return true;
}

bool Parser::scanQualifiedName(uint32_t& index) {
    auto next = peek(index);
    if (next.kind != TokenKind::Identifier && next.kind != TokenKind::UnitSystemName)
        return false;

    index++;
    while (true) {
        if (peek(index).kind == TokenKind::Hash) {
            // scan parameter value assignment
            if (peek(++index).kind != TokenKind::OpenParenthesis)
                return false;
            index++;
            if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                           TokenKind::CloseParenthesis))
                return false;
        }

        if (peek(index).kind != TokenKind::DoubleColon)
            break;

        index++;
        if (peek(index++).kind != TokenKind::Identifier)
            return false;
    }
    return true;
}

void Parser::errorIfAttributes(span<AttributeInstanceSyntax*> attributes) {
    if (!attributes.empty())
        addDiag(diag::AttributesNotAllowed, peek().location());
}

void Parser::checkBlockNames(string_view begin, string_view end, SourceLocation loc) {
    if (begin.empty() || end.empty())
        return;

    if (begin != end)
        addDiag(diag::EndNameMismatch, loc) << end << begin;
}

void Parser::checkBlockNames(Token nameToken, const NamedBlockClauseSyntax* endBlock) {
    if (!endBlock || !nameToken)
        return;

    checkBlockNames(nameToken.valueText(), endBlock->name.valueText(), endBlock->name.location());
}

void Parser::checkBlockNames(const NamedBlockClauseSyntax* beginBlock,
                             const NamedBlockClauseSyntax* endBlock,
                             const NamedLabelSyntax* label) {
    Token name;
    if (beginBlock) {
        name = beginBlock->name;
        if (label) {
            addDiag(diag::LabelAndName, label->name.location()) << name.range();
            return;
        }
    }
    else if (label) {
        name = label->name;
    }

    if (!endBlock)
        return;

    if (!name) {
        addDiag(diag::EndNameNotEmpty, endBlock->name.location());
        return;
    }

    checkBlockNames(name.valueText(), endBlock->name.valueText(), endBlock->name.location());
}

void Parser::handleTooDeep() {
    addDiag(diag::ParseTreeTooDeep, peek().location());
    throw RecursionException("");
}

} // namespace slang
