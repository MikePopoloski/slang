//------------------------------------------------------------------------------
// Parser.cpp
// SystemVerilog language parser
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/Parser.h"

#include "slang/diagnostics/ParserDiags.h"

namespace slang::parsing {

using namespace syntax;

Parser::Parser(Preprocessor& preprocessor, const Bag& options) :
    ParserBase::ParserBase(preprocessor), factory(alloc),
    parseOptions(options.getOrDefault<ParserOptions>()),
    numberParser(getDiagnostics(), alloc, parseOptions.languageVersion) {
}

SyntaxNode& Parser::parseGuess() {
    // First try to parse as some kind of declaration.
    if (isMember()) {
        bool anyLocalModules = false;
        auto member = parseMember(SyntaxKind::CompilationUnit, anyLocalModules);
        SLANG_ASSERT(member);
        member->previewNode = std::exchange(previewNode, nullptr);
        return *member;
    }

    // Try to parse as an expression if possible.
    if (isPossibleExpression(peek().kind)) {
        auto& expr = parseExpression();
        if (peek(TokenKind::Semicolon))
            consume();

        return expr;
    }

    // Now try to parse as a statement.
    auto& statement = parseStatement(/* allowEmpty */ true);
    statement.previewNode = std::exchange(previewNode, nullptr);

    // It might not have been a statement at all, in which case try a whole compilation unit
    if (statement.kind == SyntaxKind::EmptyStatement &&
        statement.as<EmptyStatementSyntax>().semicolon.isMissing()) {

        getDiagnostics().pop_back();
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

ParserMetadata&& Parser::getMetadata() {
    if (meta.eofToken.kind != TokenKind::EndOfFile && peek(TokenKind::EndOfFile))
        meta.eofToken = consume();

    return std::move(meta);
}

Token Parser::parseLifetime() {
    auto kind = peek().kind;
    if (kind == TokenKind::StaticKeyword || kind == TokenKind::AutomaticKeyword)
        return consume();
    return Token();
}

AnsiPortListSyntax& Parser::parseAnsiPortList(Token openParen) {
    Token closeParen;
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleAnsiPort, isEndOfParenList>(buffer, TokenKind::CloseParenthesis,
                                                    TokenKind::Comma, closeParen,
                                                    RequireItems::False, diag::ExpectedAnsiPort,
                                                    [this] { return &parseAnsiPort(); });

    auto& result = factory.ansiPortList(openParen, buffer.copy(alloc), closeParen);
    result.previewNode = std::exchange(previewNode, nullptr);
    return result;
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
        if (peek(TokenKind::Dot) && peek(1).kind == TokenKind::Star) {
            auto dot = consume();
            auto star = consume();
            ports = &factory.wildcardPortList(openParen, dot, star,
                                              expect(TokenKind::CloseParenthesis));
        }
        else if (isNonAnsiPort()) {
            Token closeParen;
            SmallVector<TokenOrSyntax, 8> buffer;
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

    if (moduleKeyword.kind == TokenKind::PackageKeyword) {
        std::optional<SourceRange> errorRange;
        if (!imports.empty())
            errorRange = imports[0]->sourceRange();
        else if (parameterList)
            errorRange = parameterList->sourceRange();
        else if (ports)
            errorRange = ports->sourceRange();

        if (errorRange)
            addDiag(diag::InvalidPackageDecl, *errorRange);
    }
    else if (!imports.empty() && !parameterList && !ports) {
        addDiag(diag::ExpectedPortList, peek().location());
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
    std::span<TokenOrSyntax> parameters;
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
        std::span<TokenOrSyntax> items;

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
        return factory.emptyNonAnsiPort(placeholderToken());

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

    return factory.implicitNonAnsiPort(parsePortExpression());
}

PortHeaderSyntax& Parser::parsePortHeader(Token constKeyword, Token direction) {
    auto kind = peek().kind;

    if (!constKeyword) {
        if (isNetType(kind)) {
            auto netType = consume();
            auto& dataType = parseDataType(TypeOptions::AllowImplicit);

            if (netType.kind == TokenKind::InterconnectKeyword &&
                (dataType.kind != SyntaxKind::ImplicitType ||
                 dataType.as<ImplicitTypeSyntax>().signing)) {
                addDiag(diag::InterconnectTypeSyntax, dataType.sourceRange());
            }

            return factory.netPortHeader(direction, netType, dataType);
        }

        if (kind == TokenKind::InterfaceKeyword) {
            if (direction)
                addDiag(diag::DirectionOnInterfacePort, direction.location());

            auto keyword = consume();
            return factory.interfacePortHeader(keyword, parseDotMemberClause());
        }
    }

    if (kind == TokenKind::VarKeyword) {
        auto varKeyword = consume();
        return factory.variablePortHeader(constKeyword, direction, varKeyword,
                                          parseDataType(TypeOptions::AllowImplicit));
    }

    if (kind == TokenKind::Identifier) {
        // could be a bunch of different things here; scan ahead to see
        if (!constKeyword && peek(1).kind == TokenKind::Dot &&
            peek(2).kind == TokenKind::Identifier && peek(3).kind == TokenKind::Identifier) {
            auto name = consume();
            InterfacePortHeaderSyntax* header =
                &factory.interfacePortHeader(name, parseDotMemberClause());
            meta.interfacePorts.push_back(header);
            return *header;
        }

        DataTypeSyntax* type;
        if (!isPlainPortName())
            type = &parseDataType();
        else
            type = &factory.implicitType(Token(), nullptr, placeholderToken());

        return factory.variablePortHeader(constKeyword, direction, Token(), *type);
    }

    // assume we have some kind of data type here
    return factory.variablePortHeader(constKeyword, direction, Token(),
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

    auto& header = parsePortHeader(Token(), direction);
    auto& declarator = parseDeclarator();
    return factory.implicitAnsiPort(attributes, header, declarator);
}

PortDeclarationSyntax& Parser::parsePortDeclaration(AttrList attributes) {
    Token constKeyword = consumeIf(TokenKind::ConstKeyword);
    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    // Callers must ensure we don't call with 'const' unless also 'ref'.
    SLANG_ASSERT(!constKeyword || direction.kind == TokenKind::RefKeyword);

    auto& header = parsePortHeader(constKeyword, direction);

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
    if (kind == TokenKind::Dot || kind == TokenKind::OpenBrace || kind == TokenKind::Comma)
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
            SLANG_ASSERT(selector);
            specifier = &factory.rangeDimensionSpecifier(*selector);
            break;
        }
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return &factory.variableDimension(openBracket, specifier, closeBracket);
}

std::span<VariableDimensionSyntax*> Parser::parseDimensionList() {
    SmallVector<VariableDimensionSyntax*> buffer;
    while (true) {
        auto dim = parseDimension();
        if (!dim)
            break;
        buffer.push_back(dim);
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

    Token taggedOrSoft;
    if (peek(TokenKind::TaggedKeyword) || peek(TokenKind::SoftKeyword))
        taggedOrSoft = consume();

    auto packed = consumeIf(TokenKind::PackedKeyword);
    auto signing = parseSigning();
    auto openBrace = expect(TokenKind::OpenBrace);

    Token closeBrace;
    SmallVector<StructUnionMemberSyntax*> buffer;

    if (openBrace.isMissing())
        closeBrace = missingToken(TokenKind::CloseBrace, openBrace.location());
    else {
        auto curr = peek();
        while (isPossibleStructMember(curr.kind)) {
            auto attributes = parseAttributes();

            Token randomQualifier;
            switch (peek().kind) {
                case TokenKind::RandKeyword:
                case TokenKind::RandCKeyword:
                    randomQualifier = consume();
                    if (packed)
                        addDiag(diag::RandOnPackedMember, randomQualifier.range());
                    else if (keyword.kind == TokenKind::UnionKeyword)
                        addDiag(diag::RandOnUnionMember, randomQualifier.range());
                    break;
                default:
                    break;
            }

            bitmask<TypeOptions> typeOptions;
            if (taggedOrSoft.kind == TokenKind::TaggedKeyword &&
                keyword.kind == TokenKind::UnionKeyword) {
                typeOptions = TypeOptions::AllowVoid;
            }

            auto& type = parseDataType(typeOptions);

            Token semi;
            auto declarators = parseDeclarators(semi);

            buffer.push_back(
                &factory.structUnionMember(attributes, randomQualifier, type, declarators, semi));
            buffer.back()->previewNode = std::exchange(previewNode, nullptr);

            // If we failed to consume any tokens for this member, skip whatever token is
            // in the way, otherwise we will loop forever.
            if (type.kind == SyntaxKind::ImplicitType && declarators.empty() &&
                peek().location() == curr.location()) {
                skipToken({});
            }

            curr = peek();
        }
        closeBrace = expect(TokenKind::CloseBrace);

        if (buffer.empty() && !closeBrace.isMissing())
            addDiag(diag::ExpectedMember, closeBrace.location());
    }

    auto dims = parseDimensionList();
    if (!packed) {
        if (!dims.empty()) {
            SourceRange range{dims.front()->getFirstToken().location(),
                              dims.back()->getLastToken().range().end()};
            addDiag(diag::PackedDimsOnUnpacked, range);
        }

        if (signing)
            addDiag(diag::UnpackedSigned, signing.range());
    }

    if (keyword.kind == TokenKind::StructKeyword && taggedOrSoft.valid()) {
        addDiag(diag::TaggedStruct, taggedOrSoft.range()) << taggedOrSoft.valueText();
    }
    else if (taggedOrSoft.kind == TokenKind::SoftKeyword &&
             parseOptions.languageVersion < LanguageVersion::v1800_2023) {
        addDiag(diag::WrongLanguageVersion, taggedOrSoft.range())
            << toString(parseOptions.languageVersion);
    }

    return factory.structUnionType(syntaxKind, keyword, taggedOrSoft, packed, signing, openBrace,
                                   buffer.copy(alloc), closeBrace, dims);
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
    std::span<TokenOrSyntax> declarators;
    if (openBrace.isMissing())
        closeBrace = missingToken(TokenKind::CloseBrace, openBrace.location());
    else
        declarators = parseDeclarators<isCloseBrace>(TokenKind::CloseBrace, closeBrace);

    return factory.enumType(keyword, baseType, openBrace, declarators, closeBrace,
                            parseDimensionList());
}

DataTypeSyntax& Parser::parseDataType(bitmask<TypeOptions> options) {
    if (peek(TokenKind::WireKeyword))
        skipToken(diag::WireDataType);

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
        case TokenKind::EnumKeyword: {
            auto& result = parseEnum();
            result.previewNode = std::exchange(previewNode, &result);
            return result;
        }
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
            if (scanQualifiedName(index, /* allowNew */ false) && scanDimensionList(index) &&
                peek(index).kind == TokenKind::Identifier) {
                return factory.namedType(parseName());
            }

            return factory.implicitType(Token(), nullptr, placeholderToken());
        }
    }

    auto signing = parseSigning();
    auto dimensions = parseDimensionList();

    if ((options & TypeOptions::AllowImplicit) == 0)
        addDiag(diag::ImplicitNotAllowed, peek().location());

    return factory.implicitType(signing, dimensions, placeholderToken());
}

static bool isHighZ(Token t) {
    return t.kind == TokenKind::HighZ0Keyword || t.kind == TokenKind::HighZ1Keyword;
}

DriveStrengthSyntax* Parser::parseDriveStrength() {
    if (!peek(TokenKind::OpenParenthesis))
        return nullptr;

    auto expectStrength = [&](TokenKind defaultKind) {
        Token next = peek();
        if (isDriveStrength(next.kind))
            return consume();

        addDiag(diag::ExpectedNetStrength, next.location());
        return missingToken(defaultKind, next.location());
    };

    auto openParen = consume();
    auto strength0 = expectStrength(TokenKind::Strong1Keyword);
    auto comma = expect(TokenKind::Comma);
    auto strength1 = expectStrength(TokenKind::Strong0Keyword);
    auto closeParen = expect(TokenKind::CloseParenthesis);

    if (isStrength0(strength0.kind) == isStrength0(strength1.kind))
        addDiag(diag::DriveStrengthInvalid, strength1.range()) << strength0.range();
    else if (isHighZ(strength0) && isHighZ(strength1))
        addDiag(diag::DriveStrengthHighZ, strength1.range()) << strength0.range();

    return &factory.driveStrength(openParen, strength0, comma, strength1, closeParen);
}

NetStrengthSyntax* Parser::parsePullStrength(Token type) {
    if (!peek(TokenKind::OpenParenthesis) || !isDriveStrength(peek(1).kind))
        return nullptr;

    auto errorIfHighZ = [&](Token t) {
        if (isHighZ(t))
            addDiag(diag::PullStrengthHighZ, t.range());
    };

    if (peek(2).kind == TokenKind::Comma) {
        auto strength = parseDriveStrength();
        errorIfHighZ(strength->strength0);
        errorIfHighZ(strength->strength1);
        return strength;
    }

    auto openParen = consume();
    auto strength = consume();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    errorIfHighZ(strength);
    if (!isHighZ(strength)) {
        bool isPulldown = type.kind == TokenKind::PullDownKeyword;
        if (isStrength0(strength.kind) != isPulldown)
            addDiag(diag::InvalidPullStrength, strength.range()) << type.valueText();
    }

    return &factory.pullStrength(openParen, strength, closeParen);
}

TimingControlSyntax* Parser::parseDelay3() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    if (peek(1).kind != TokenKind::OpenParenthesis)
        return parseTimingControl();

    auto hash = consume();
    auto openParen = consume();
    auto& delay1 = parseMinTypMaxExpression();

    Token comma1, comma2;
    ExpressionSyntax* delay2 = nullptr;
    ExpressionSyntax* delay3 = nullptr;

    if (peek(TokenKind::Comma)) {
        comma1 = consume();
        delay2 = &parseMinTypMaxExpression();

        if (peek(TokenKind::Comma)) {
            comma2 = consume();
            delay3 = &parseMinTypMaxExpression();
        }
    }

    return &factory.delay3(hash, openParen, delay1, comma1, delay2, comma2, delay3,
                           expect(TokenKind::CloseParenthesis));
}

MemberSyntax& Parser::parseNetDeclaration(AttrList attributes) {
    auto netType = consume();
    if (netType.kind == TokenKind::Identifier) {
        // We will only be called in this case if isNetDeclaration returns true, which
        // itself will only do so for an identifier if the following token is a hash,
        // indicating a timing control.
        auto delay = parseTimingControl();
        SLANG_ASSERT(delay);

        Token semi;
        auto declarators = parseDeclarators(semi);

        return factory.userDefinedNetDeclaration(attributes, netType, *delay, declarators, semi);
    }

    if (peek(TokenKind::RegKeyword))
        addDiag(diag::RegAfterNettype, peek().location());

    bool hasDriveStrength = false;
    NetStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        if (isChargeStrength(peek(1).kind)) {
            if (netType.kind != TokenKind::TriRegKeyword)
                addDiag(diag::ChargeWithTriReg, peek(1).location());

            auto openParen = consume();
            auto charge = consume();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            strength = &factory.chargeStrength(openParen, charge, closeParen);
        }
        else {
            strength = parseDriveStrength();
            hasDriveStrength = true;
        }
    }

    Token expansionHint;
    if (peek(TokenKind::VectoredKeyword) || peek(TokenKind::ScalaredKeyword))
        expansionHint = consume();

    auto& type = parseDataType(TypeOptions::AllowImplicit);
    auto delay = parseDelay3();

    Token semi;
    auto declSpan = parseDeclarators(semi, /* allowMinTypMax */ false,
                                     /* requireInitializers */ hasDriveStrength);

    SeparatedSyntaxList<DeclaratorSyntax> declarators(declSpan);
    if (netType.kind == TokenKind::InterconnectKeyword) {
        if (type.kind != SyntaxKind::ImplicitType || type.as<ImplicitTypeSyntax>().signing)
            addDiag(diag::InterconnectTypeSyntax, type.sourceRange());

        if (delay && delay->kind != SyntaxKind::OneStepDelay &&
            delay->kind != SyntaxKind::DelayControl) {
            addDiag(diag::InterconnectDelaySyntax, delay->sourceRange());
        }

        for (auto decl : declarators) {
            if (decl->initializer)
                addDiag(diag::InterconnectInitializer, decl->initializer->sourceRange());
        }
    }

    return factory.netDeclaration(attributes, netType, strength, expansionHint, type, delay,
                                  declarators, semi);
}

ForwardTypeRestrictionSyntax* Parser::parseTypeRestriction(bool isExpected) {
    switch (peek().kind) {
        case TokenKind::EnumKeyword:
        case TokenKind::StructKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::ClassKeyword:
            if (isExpected ||
                (peek(1).kind == TokenKind::Identifier && peek(2).kind == TokenKind::Semicolon)) {
                return &factory.forwardTypeRestriction(consume(), Token());
            }
            break;
        case TokenKind::InterfaceKeyword: {
            auto interfaceKeyword = consume();
            auto classKeyword = expect(TokenKind::ClassKeyword);
            return &factory.forwardTypeRestriction(interfaceKeyword, classKeyword);
        }
        default:
            break;
    }
    return nullptr;
}

MemberSyntax& Parser::parseVariableDeclaration(AttrList attributes) {
    switch (peek().kind) {
        case TokenKind::TypedefKeyword: {
            auto typedefKeyword = consume();
            auto restriction = parseTypeRestriction(/* isExpected */ false);
            if (restriction ||
                (peek(TokenKind::Identifier) && peek(1).kind == TokenKind::Semicolon)) {
                auto name = expect(TokenKind::Identifier);
                return factory.forwardTypedefDeclaration(attributes, typedefKeyword, restriction,
                                                         name, expect(TokenKind::Semicolon));
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
            auto portList = parseAssertionItemPortList(SyntaxKind::LetDeclaration);
            auto equals = expect(TokenKind::Equals);
            auto& expr = parseExpression();
            return factory.letDeclaration(attributes, let, identifier, portList, equals, expr,
                                          expect(TokenKind::Semicolon));
        }
        case TokenKind::ImportKeyword:
            return parseImportDeclaration(attributes);
        case TokenKind::NetTypeKeyword:
            return parseNetTypeDecl(attributes);
        default:
            return parseDataDeclaration(attributes);
    }
}

DataDeclarationSyntax& Parser::parseDataDeclaration(AttrList attributes) {
    SmallVector<Token, 4> modifiers;
    SmallMap<TokenKind, Token, 4> modifierSet;
    Token lastLifetime;
    bool hasVar = false;
    bool errorDup = false;
    bool errorLifetime = false;
    bool errorOrdering = false;

    while (isDeclarationModifier(peek().kind)) {
        Token t = consume();
        modifiers.push_back(t);
        if (t.kind == TokenKind::VarKeyword)
            hasVar = true;

        if (auto [it, inserted] = modifierSet.emplace(t.kind, t); !inserted) {
            if (!errorDup) {
                auto& diag = addDiag(diag::DuplicateDeclModifier, t.range());
                diag << t.rawText() << it->second.range();
                errorDup = true;
            }
            continue;
        }

        if (SyntaxFacts::isLifetimeModifier(t.kind)) {
            if (lastLifetime) {
                if (!errorLifetime) {
                    auto& diag = addDiag(diag::DeclModifierConflict, t.range());
                    diag << t.rawText();
                    diag << lastLifetime.rawText() << lastLifetime.range();
                    errorLifetime = true;
                }
                continue;
            }
            lastLifetime = t;
        }

        if (!errorOrdering && modifiers.size() > 1) {
            Token prev = modifiers[modifiers.size() - 2];
            if (!SyntaxFacts::isModifierAllowedAfter(t.kind, prev.kind)) {
                auto& diag = addDiag(diag::DeclModifierOrdering, t.range());
                diag << t.rawText();
                diag << prev.rawText() << prev.range();
                errorOrdering = true;
            }
        }
    }

    auto& dataType = parseDataType(hasVar ? TypeOptions::AllowImplicit : TypeOptions::None);
    if (dataType.kind == SyntaxKind::TypeReference && !hasVar)
        addDiag(diag::TypeRefDeclVar, dataType.getFirstToken().location());

    Token semi;
    auto declarators = parseDeclarators(semi);

    return factory.dataDeclaration(attributes, modifiers.copy(alloc), dataType, declarators, semi);
}

LocalVariableDeclarationSyntax& Parser::parseLocalVariableDeclaration() {
    auto var = consumeIf(TokenKind::VarKeyword);
    auto& dataType = parseDataType(var ? TypeOptions::AllowImplicit : TypeOptions::None);
    if (dataType.kind == SyntaxKind::TypeReference && !var)
        addDiag(diag::TypeRefDeclVar, dataType.getFirstToken().location());

    Token semi;
    auto declarators = parseDeclarators(semi);

    return factory.localVariableDeclaration(nullptr, var, dataType, declarators, semi);
}

DeclaratorSyntax& Parser::parseDeclarator(bool allowMinTypMax, bool requireInitializers) {
    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &factory.equalsValueClause(equals, allowMinTypMax ? parseMinTypMaxExpression()
                                                                        : parseExpression());
    }
    else if (requireInitializers) {
        addDiag(diag::InitializerRequired, name.location());
    }

    return factory.declarator(name, dimensions, initializer);
}

template<bool (*IsEnd)(TokenKind)>
std::span<TokenOrSyntax> Parser::parseDeclarators(TokenKind endKind, Token& end,
                                                  bool allowMinTypMax, bool requireInitializers) {
    SmallVector<TokenOrSyntax, 4> buffer;
    parseList<isIdentifierOrComma, IsEnd>(buffer, endKind, TokenKind::Comma, end,
                                          RequireItems::True, diag::ExpectedDeclarator,
                                          [this, allowMinTypMax, requireInitializers] {
                                              return &parseDeclarator(allowMinTypMax,
                                                                      requireInitializers);
                                          });

    return buffer.copy(alloc);
}

std::span<TokenOrSyntax> Parser::parseDeclarators(Token& semi, bool allowMinTypMax,
                                                  bool requireInitializers) {
    return parseDeclarators<isNotIdOrComma>(TokenKind::Semicolon, semi, allowMinTypMax,
                                            requireInitializers);
}

Parser::AttrList Parser::parseAttributes() {
    SmallVector<AttributeInstanceSyntax*> buffer;
    while (isStartOfAttrs(0)) {
        Token openParen = consume();
        Token closeParen, openStar, closeStar;

        std::span<TokenOrSyntax> list;
        parseList<isIdentifierOrComma, isEndOfAttribute>(
            TokenKind::Star, TokenKind::Star, TokenKind::Comma, openStar, list, closeStar,
            RequireItems::True, diag::ExpectedAttribute, [this] { return &parseAttributeSpec(); });

        if (!closeStar.isMissing()) {
            closeParen = expect(TokenKind::CloseParenthesis);
            if (!closeParen.isMissing() && !closeParen.trivia().empty())
                addDiag(diag::ExpectedToken, closeStar.location()) << "*)"sv;
        }

        buffer.push_back(
            &factory.attributeInstance(openParen, openStar, list, closeStar, closeParen));
    }
    return buffer.copy(alloc);
}

AttributeSpecSyntax& Parser::parseAttributeSpec() {
    auto name = expect(TokenKind::Identifier);

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        // Nested attributes are not allowed
        initializer = &factory.equalsValueClause(
            equals, parseSubExpression(ExpressionOptions::DisallowAttrs, 0));
    }

    return factory.attributeSpec(name, initializer);
}

NetTypeDeclarationSyntax& Parser::parseNetTypeDecl(AttrList attributes) {
    auto keyword = consume();
    auto& type = parseDataType();
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
    ParameterDeclarationBaseSyntax* result;
    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword))
        result = &parseParameterDecl(consume(), nullptr);
    else
        result = &parseParameterDecl(Token(), nullptr);

    result->previewNode = std::exchange(previewNode, nullptr);
    return *result;
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
        auto restriction = parseTypeRestriction(/* isExpected */ true);
        if (restriction && parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, restriction->sourceRange())
                << toString(parseOptions.languageVersion);
        }

        SmallVector<TokenOrSyntax, 4> decls;
        if (semi) {
            parseList<isIdentifierOrComma, isSemicolon>(decls, TokenKind::Semicolon,
                                                        TokenKind::Comma, *semi, RequireItems::True,
                                                        diag::ExpectedParameterPort,
                                                        [this] { return &parseTypeAssignment(); });
        }
        else {
            while (true) {
                decls.push_back(&parseTypeAssignment());
                if (!peek(TokenKind::Comma) || peek(1).kind != TokenKind::Identifier ||
                    (peek(2).kind != TokenKind::Equals && peek(2).kind != TokenKind::Comma)) {
                    break;
                }

                decls.push_back(consume());
            }
        }

        return factory.typeParameterDeclaration(keyword, typeKeyword, restriction,
                                                decls.copy(alloc));
    }
    else {
        auto& type = parseDataType(TypeOptions::AllowImplicit);

        // If the semi pointer is given, we should parse a simple list of decls.
        // Otherwise we're in a parameter port list and don't know if we'll encounter
        // other non-decl things, so do the parsing manually.
        std::span<TokenOrSyntax> decls;
        if (semi) {
            decls = parseDeclarators(*semi, /* allowMinTypMax */ true);
        }
        else {
            SmallVector<TokenOrSyntax, 2> buffer;
            while (true) {
                buffer.push_back(&parseDeclarator(/* allowMinTypMax */ true));
                if (!peek(TokenKind::Comma) || peek(1).kind != TokenKind::Identifier)
                    break;

                // We need to disambiguate here between another decl which has an optional
                // unpacked dimension list from a totally new parameter being declared with
                // an identifier type and an optional packed dimension list. If it's not the
                // former we will bail out and let our parent parse a new parameter.
                uint32_t index = 2;
                if (!scanDimensionList(index))
                    break;

                if (auto nk = peek(index).kind; nk != TokenKind::Comma && nk != TokenKind::Equals &&
                                                nk != TokenKind::CloseParenthesis) {
                    break;
                }

                buffer.push_back(consume());
            }
            decls = buffer.copy(alloc);
        }

        return factory.parameterDeclaration(keyword, type, decls);
    }
}

PortConnectionSyntax& Parser::parsePortConnection() {
    auto attributes = parseAttributes();

    // Allow for empty port connections.
    if (peek(TokenKind::Comma) || peek(TokenKind::CloseParenthesis))
        return factory.emptyPortConnection(attributes, placeholderToken());

    if (peek(TokenKind::Dot)) {
        auto dot = consume();

        if (peek(TokenKind::Star))
            return factory.wildcardPortConnection(attributes, dot, consume());

        auto name = expect(TokenKind::Identifier);

        PropertyExprSyntax* expr = nullptr;
        Token openParen, closeParen;

        if (peek(TokenKind::OpenParenthesis)) {
            openParen = consume();
            if (!peek(TokenKind::CloseParenthesis))
                expr = &parsePropertyExpr(0);

            closeParen = expect(TokenKind::CloseParenthesis);
        }
        return factory.namedPortConnection(attributes, dot, name, openParen, expr, closeParen);
    }
    return factory.orderedPortConnection(attributes, parsePropertyExpr(0));
}

bool Parser::isMember() {
    // Any attributes found should indicate a member.
    uint32_t index = 0;
    scanAttributes(index);
    if (index > 0)
        return true;

    if (isHierarchyInstantiation(/* requireName */ true) || isNetDeclaration() ||
        isVariableDeclaration()) {
        return true;
    }

    switch (peek().kind) {
        case TokenKind::GenerateKeyword:
        case TokenKind::TimeUnitKeyword:
        case TokenKind::TimePrecisionKeyword:
        case TokenKind::ModuleKeyword:
        case TokenKind::MacromoduleKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::PackageKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::ModPortKeyword:
        case TokenKind::BindKeyword:
        case TokenKind::SpecParamKeyword:
        case TokenKind::AliasKeyword:
        case TokenKind::SpecifyKeyword:
        case TokenKind::AssignKeyword:
        case TokenKind::InitialKeyword:
        case TokenKind::FinalKeyword:
        case TokenKind::AlwaysKeyword:
        case TokenKind::AlwaysCombKeyword:
        case TokenKind::AlwaysFFKeyword:
        case TokenKind::AlwaysLatchKeyword:
        case TokenKind::GenVarKeyword:
        case TokenKind::TaskKeyword:
        case TokenKind::FunctionKeyword:
        case TokenKind::CoverGroupKeyword:
        case TokenKind::ClassKeyword:
        case TokenKind::VirtualKeyword:
        case TokenKind::DefParamKeyword:
        case TokenKind::ImportKeyword:
        case TokenKind::ExportKeyword:
        case TokenKind::PropertyKeyword:
        case TokenKind::SequenceKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::GlobalKeyword:
        case TokenKind::DefaultKeyword:
        case TokenKind::ClockingKeyword:
        case TokenKind::ConstraintKeyword:
        case TokenKind::PrimitiveKeyword:
        case TokenKind::ConfigKeyword:
        case TokenKind::Semicolon:
            return true;
        default:
            return isGateType(peek().kind);
    }
}

bool Parser::isPortDeclaration(bool inStatement) {
    uint32_t index = 0;
    if (!scanAttributes(index))
        return false;

    TokenKind kind = peek(index).kind;
    if (kind == TokenKind::ConstKeyword && peek(index + 1).kind == TokenKind::RefKeyword)
        return true;

    // non-ansi interface port declarations are of the form:
    // interface_identifier . modport_identifier list_of_interface_identifiers
    if (!inStatement && kind == TokenKind::Identifier && peek(index + 1).kind == TokenKind::Dot &&
        peek(index + 2).kind == TokenKind::Identifier &&
        peek(index + 3).kind == TokenKind::Identifier) {
        return true;
    }

    return isPortDirection(kind);
}

bool Parser::isNetDeclaration() {
    if (isNetType(peek().kind))
        return true;

    // This can be a user-defined nettype with a delay value here.
    // This can look pretty similar to a hierarchical instantiation,
    // so try hard to disambiguate them here.
    uint32_t index = 0;
    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    if (peek(index++).kind != TokenKind::Hash)
        return false;

    // This case will be handled later because we have to disambiguate with
    // class parameter assignments.
    if (peek(index).kind == TokenKind::OpenParenthesis)
        return false;

    switch (peek(index++).kind) {
        case TokenKind::IntegerLiteral:
        case TokenKind::OneStep:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
            break;
        case TokenKind::Identifier:
        case TokenKind::UnitSystemName:
            if (peek(index).kind == TokenKind::Colon) {
                if (peek(++index).kind != TokenKind::Identifier)
                    return false;
                index++;
            }
            break;
        default:
            return false;
    }

    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    TokenKind kind = peek(index).kind;
    return kind == TokenKind::Comma || kind == TokenKind::Equals || kind == TokenKind::Semicolon;
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
            return true;

        // Static keyword *should* always be a variable, but it could accidentally
        // be an attempt at an out-of-block function declaration, or it could legitimately
        // be an out-of-block constraint declaration.
        case TokenKind::StaticKeyword: {
            auto next = peek(index + 1);
            return next.kind != TokenKind::FunctionKeyword && next.kind != TokenKind::TaskKeyword &&
                   next.kind != TokenKind::ConstraintKeyword;
        }

        // either an import of a package or a DPI import
        case TokenKind::ImportKeyword:
            return peek(index + 1).kind != TokenKind::StringLiteral;

        // this could be a virtual interface, a virtual class declaration, or a virtual function
        case TokenKind::VirtualKeyword:
            if (peek(++index).kind == TokenKind::InterfaceKeyword)
                return true;
            if (!scanQualifiedName(index, /* allowNew */ false))
                return false;
            if (peek(index).kind == TokenKind::Dot)
                return true;
            return peek(index).kind == TokenKind::Identifier;

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

        // if this is the type operator it's technically not allowed to be a variable
        // declaration without a "var" prefix, but we'll try to allow it anyway and
        // diagnose it later with a better error message.
        case TokenKind::TypeKeyword: {
            if (peek(++index).kind != TokenKind::OpenParenthesis)
                return false;

            index++;
            if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                           TokenKind::CloseParenthesis)) {
                return false;
            }
            return peek(index).kind == TokenKind::Identifier;
        }

        default:
            break;
    }

    if (!scanQualifiedName(index, /* allowNew */ false))
        return false;

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // next token is the decider; declarations must have an identifier here
    // and there can't be an open parenthesis right after it.
    return peek(index).kind == TokenKind::Identifier &&
           peek(index + 1).kind != TokenKind::OpenParenthesis;
}

bool Parser::isLocalVariableDeclaration() {
    uint32_t index = 0;
    auto kind = peek(index).kind;
    switch (kind) {
        case TokenKind::VarKeyword:
        case TokenKind::CHandleKeyword:
        case TokenKind::EventKeyword:
        case TokenKind::StructKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::EnumKeyword:
        case TokenKind::VirtualKeyword:
            return true;

        // some cases might be a cast expression
        case TokenKind::StringKeyword:
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

        // if this is the type operator it's technically not allowed to be a variable
        // declaration without a "var" prefix, but we'll try to allow it anyway and
        // diagnose it later with a better error message.
        case TokenKind::TypeKeyword: {
            if (peek(++index).kind != TokenKind::OpenParenthesis)
                return false;

            index++;
            if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                           TokenKind::CloseParenthesis)) {
                return false;
            }
            return peek(index).kind == TokenKind::Identifier;
        }

        default:
            break;
    }

    if (!scanQualifiedName(index, /* allowNew */ false))
        return false;

    // might be a list of dimensions here
    if (!scanDimensionList(index))
        return false;

    // next token is the decider; declarations must have an identifier here
    return peek(index).kind == TokenKind::Identifier;
}

bool Parser::isHierarchyInstantiation(bool requireName) {
    uint32_t index = 0;
    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    // skip over std::optional parameter value assignment
    if (peek(index).kind == TokenKind::Hash) {
        if (peek(++index).kind != TokenKind::OpenParenthesis)
            return false;

        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis,
                                       TokenKind::CloseParenthesis)) {
            return false;
        }
    }

    if (peek(index).kind == TokenKind::Identifier) {
        index++;
        if (!scanDimensionList(index))
            return false;
    }
    else if (requireName) {
        return false;
    }

    // A parenthesis here indicates a start of a hierarchical instantiation,
    // unless there's a drive strength token immediately after it.
    if (peek(index++).kind != TokenKind::OpenParenthesis)
        return false;

    return !isDriveStrength(peek(index).kind);
}

bool Parser::scanDimensionList(uint32_t& index) {
    while (peek(index).kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return false;
    }
    return true;
}

bool Parser::scanQualifiedName(uint32_t& index, bool allowNew) {
    auto next = peek(index);
    if (next.kind != TokenKind::Identifier && next.kind != TokenKind::UnitSystemName &&
        (!allowNew || next.kind != TokenKind::NewKeyword)) {
        return false;
    }

    while (true) {
        if (peek(++index).kind == TokenKind::Hash) {
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

        next = peek(++index);
        if (next.kind != TokenKind::Identifier && (!allowNew || next.kind != TokenKind::NewKeyword))
            return false;
    }
    return true;
}

bool Parser::scanAttributes(uint32_t& index) {
    while (isStartOfAttrs(index)) {
        // scan over attributes
        index++;
        while (true) {
            auto kind = peek(++index).kind;
            if (kind == TokenKind::EndOfFile)
                return false;
            if (kind == TokenKind::Star && peek(index + 1).kind == TokenKind::CloseParenthesis)
                break;
        }
        index += 2;
    }
    return true;
}

bool Parser::isStartOfAttrs(uint32_t index) {
    if (peek(index).kind == TokenKind::OpenParenthesis) {
        auto t = peek(index + 1);
        return t.kind == TokenKind::Star && t.trivia().empty();
    }
    return false;
}

void Parser::errorIfAttributes(AttrList attributes) {
    if (!attributes.empty()) {
        auto last = attributes.back()->getLastToken();
        SourceRange range{attributes.front()->getFirstToken().location(),
                          last.location() + last.rawText().length()};
        addDiag(diag::AttributesNotAllowed, range);
    }
}

void Parser::checkBlockNames(std::string_view begin, std::string_view end, SourceLocation loc) {
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
    SLANG_THROW(RecursionException(""));
}

} // namespace slang::parsing
