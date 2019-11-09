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
        return factory.netPortHeader(direction, netType, parseDataType(TypeOptions::AllowImplicit));
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
                                          parseDataType(TypeOptions::AllowImplicit));
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
            type = &parseDataType();
        else
            type = &factory.implicitType(Token(), nullptr);

        return factory.variablePortHeader(direction, Token(), *type);
    }

    // assume we have some kind of data type here
    return factory.variablePortHeader(direction, Token(),
                                      parseDataType(TypeOptions::AllowImplicit));
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

PortDeclarationSyntax& Parser::parsePortDeclaration(AttrList attributes) {
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
                                                TokenKind::CloseBracket)) {
            return true; // if we see nonsense, we'll recover by pretending this is a plain port
        }
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
                                                TokenKind::CloseBracket)) {
            return false;
        }

        kind = peek(index).kind;
    }

    // found the end; comma or close paren means this is a non-ansi port
    return kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis;
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

            auto& type = parseDataType();

            Token semi;
            auto declarators = parseDeclarators(semi);

            buffer.append(
                &factory.structUnionMember(attributes, randomQualifier, type, declarators, semi));

            if (type.kind == SyntaxKind::ImplicitType && declarators.empty())
                skipToken({});

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
    if (!peek(TokenKind::OpenBrace)) {
        baseType = &parseDataType();
        if (!IntegerTypeSyntax::isKind(baseType->kind) && baseType->kind != SyntaxKind::NamedType)
            addDiag(diag::ExpectedEnumBase, baseType->getFirstToken().location());
    }

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

DataTypeSyntax& Parser::parseDataType(bitmask<TypeOptions> options) {
    auto kind = peek().kind;
    auto type = getIntegerType(kind);
    if (type != SyntaxKind::Unknown) {
        auto keyword = consume();
        auto signing = parseSigning();
        return factory.integerType(type, keyword, signing, parseDimensionList());
    }

    type = getKeywordType(kind);
    if (type != SyntaxKind::Unknown) {
        if (type == SyntaxKind::VoidType && (options & TypeOptions::AllowVoid) == 0)
            addDiag(diag::VoidNotAllowed, peek().location());
        return factory.keywordType(type, consume());
    }

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
        if ((options & TypeOptions::AllowImplicit) == 0)
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

    if ((options & TypeOptions::AllowImplicit) == 0)
        addDiag(diag::ImplicitNotAllowed, peek().location());

    return factory.implicitType(signing, dimensions);
}

DriveStrengthSyntax* Parser::parseDriveStrength() {
    if (!peek(TokenKind::OpenParenthesis))
        return nullptr;

    auto expectStrength = [&] {
        Token next = peek();
        if (isDriveStrength(next.kind))
            return next;

        addDiag(diag::ExpectedNetStrength, next.location());
        return missingToken(TokenKind::Supply0Keyword, next.location());
    };

    auto openParen = consume();
    auto strength0 = expectStrength();
    auto comma = expect(TokenKind::Comma);
    auto strength1 = expectStrength();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    return &factory.driveStrength(openParen, strength0, comma, strength1, closeParen);
}

MemberSyntax& Parser::parseNetDeclaration(AttrList attributes) {
    auto netType = consume();

    NetStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        if (isChargeStrength(peek(1).kind)) {
            auto openParen = consume();
            auto charge = consume();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            strength = &factory.chargeStrength(openParen, charge, closeParen);
        }
        else {
            strength = parseDriveStrength();
        }
    }

    Token expansionHint;
    if (peek(TokenKind::VectoredKeyword) || peek(TokenKind::ScalaredKeyword))
        expansionHint = consume();

    auto& type = parseDataType(TypeOptions::AllowImplicit);

    // TODO: delay control

    Token semi;
    auto declarators = parseDeclarators(semi);

    return factory.netDeclaration(attributes, netType, strength, expansionHint, type, declarators,
                                  semi);
}

MemberSyntax& Parser::parseVariableDeclaration(AttrList attributes) {
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

            auto& type = parseDataType();
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

    auto& dataType = parseDataType(hasVar ? TypeOptions::AllowImplicit : TypeOptions::None);

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

Parser::AttrList Parser::parseAttributes() {
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

NetTypeDeclarationSyntax& Parser::parseNetTypeDecl(AttrList attributes) {
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
        assignment = &factory.equalsTypeClause(equals, parseDataType());
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
        auto& type = parseDataType(TypeOptions::AllowImplicit);

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
    uint32_t index = 0;
    if (!scanAttributes(index))
        return false;

    // TODO: check for interface port declaration
    return isPortDirection(peek(index).kind);
}

bool Parser::isNetDeclaration() {
    // TODO: other net types
    return isNetType(peek().kind);
}

bool Parser::isVariableDeclaration() {
    uint32_t index = 0;
    if (!scanAttributes(index))
        return false;

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
                                       TokenKind::CloseParenthesis)) {
            return false;
        }
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
                                           TokenKind::CloseParenthesis)) {
                return false;
            }
        }

        if (peek(index).kind != TokenKind::DoubleColon)
            break;

        index++;
        if (peek(index++).kind != TokenKind::Identifier)
            return false;
    }
    return true;
}

bool Parser::scanAttributes(uint32_t& index) {
    while (peek(index).kind == TokenKind::OpenParenthesisStar) {
        // scan over attributes
        while (true) {
            auto kind = peek(++index).kind;
            if (kind == TokenKind::EndOfFile)
                return false;
            if (kind == TokenKind::StarCloseParenthesis)
                break;
        }
        index++;
    }
    return true;
}

void Parser::errorIfAttributes(AttrList attributes) {
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
