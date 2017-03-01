//------------------------------------------------------------------------------
// Parser.cpp
// SystemVerilog language parser.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Parser.h"

#include "lexing/Preprocessor.h"

namespace slang {

Parser::Parser(Preprocessor& preprocessor) :
    ParserBase::ParserBase(preprocessor),
    vectorBuilder(preprocessor.getAllocator(), getDiagnostics())
{
}

CompilationUnitSyntax& Parser::parseCompilationUnit() {
    Token eof;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndOfFile, eof, [this]() { return parseMember(); });
    return allocate<CompilationUnitSyntax>(members, eof);
}

const SyntaxNode& Parser::parseGuess() {
    // First try to parse as an instantiation
    if (isHierarchyInstantiation())
        return parseHierarchyInstantiation(parseAttributes());

    // try to parse as a variable declaration.
    if (isVariableDeclaration())
        return parseVariableDeclaration(parseAttributes());

    // Now try to parse as a statement. This will also handle plain expressions,
    // though we might get an error about a missing semicolon that we should suppress.
    auto& diagnostics = getDiagnostics();
    auto& statement = parseStatement(/* allowEmpty */ true);
    if (statement.kind == SyntaxKind::ExpressionStatement) {
        if (!diagnostics.empty() && diagnostics.back().code == DiagCode::ExpectedToken)
            diagnostics.pop();

        // Always pull the expression out for convenience.
        return statement.as<ExpressionStatementSyntax>().expr;
    }

    // It might not have been a statement at all, in which case try a whole compilation unit
    if (statement.kind == SyntaxKind::EmptyStatement && !diagnostics.empty() &&
        diagnostics.back().code == DiagCode::ExpectedStatement) {

        // If there's only one member, pull it out for convenience
        diagnostics.pop();
        const auto& unit = parseCompilationUnit();
        if (unit.members.count() == 1)
            return *unit.members[0];
        else
            return unit;
    }

    return statement;
}

ModuleDeclarationSyntax& Parser::parseModule() {
    return parseModule(parseAttributes());
}

ModuleDeclarationSyntax& Parser::parseModule(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto& header = parseModuleHeader();
    auto endKind = getModuleEndKind(header.moduleKeyword.kind);

    Token endmodule;
    auto members = parseMemberList<MemberSyntax>(endKind, endmodule, [this]() { return parseMember(); });
    return allocate<ModuleDeclarationSyntax>(
        getModuleDeclarationKind(header.moduleKeyword.kind),
        attributes,
        header,
        members,
        endmodule,
        parseNamedBlockClause()
    );
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
    if (peek(TokenKind::CloseParenthesis))
        return allocate<AnsiPortListSyntax>(openParen, nullptr, consume());

    Token closeParen;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseSeparatedList<isPossibleAnsiPort, isEndOfParenList>(
        buffer,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        closeParen,
        DiagCode::ExpectedAnsiPort,
        [this](bool) -> decltype(auto) { return parseAnsiPort(); }
    );
    return allocate<AnsiPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
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
            ports = &allocate<WildcardPortListSyntax>(openParen, dotStar, expect(TokenKind::CloseParenthesis));
        }
        else if (isNonAnsiPort()) {
            Token closeParen;
            SmallVectorSized<TokenOrSyntax, 8> buffer;
            parseSeparatedList<isPossibleNonAnsiPort, isEndOfParenList>(
                buffer,
                TokenKind::CloseParenthesis,
                TokenKind::Comma,
                closeParen,
                DiagCode::ExpectedNonAnsiPort,
                [this](bool) -> decltype(auto) { return parseNonAnsiPort(); }
            );
            ports = &allocate<NonAnsiPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
        }
        else
            ports = &parseAnsiPortList(openParen);
    }

    auto semi = expect(TokenKind::Semicolon);
    return allocate<ModuleHeaderSyntax>(getModuleHeaderKind(moduleKeyword.kind), moduleKeyword, lifetime, name, imports, parameterList, ports, semi);
}

ParameterPortListSyntax* Parser::parseParameterPortList() {
    if (!peek(TokenKind::Hash))
        return nullptr;

    auto hash = consume();

    Token openParen;
    Token closeParen;
    ArrayRef<TokenOrSyntax> parameters;
    parseSeparatedList<isPossibleParameter, isEndOfParameterList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        openParen,
        parameters,
        closeParen,
        DiagCode::ExpectedParameterPort,
        [this](bool) -> decltype(auto) { return parseParameterPort(); }
    );

    return &allocate<ParameterPortListSyntax>(hash, openParen, parameters, closeParen);
}

NonAnsiPortSyntax& Parser::parseNonAnsiPort() {
    // TODO: error if unsupported expressions are used here
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        auto name = expect(TokenKind::Identifier);
        auto openParen = expect(TokenKind::OpenParenthesis);

        ExpressionSyntax* expr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = &parsePrimaryExpression();

        return allocate<ExplicitNonAnsiPortSyntax>(dot, name, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return allocate<ImplicitNonAnsiPortSyntax>(parsePrimaryExpression());
}

PortHeaderSyntax& Parser::parsePortHeader(Token direction) {
    auto kind = peek().kind;
    if (isNetType(kind)) {
        auto netType = consume();
        return allocate<NetPortHeaderSyntax>(direction, netType, parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::InterfaceKeyword) {
        // TODO: error if direction is given
        auto keyword = consume();
        return allocate<InterfacePortHeaderSyntax>(keyword, parseDotMemberClause());
    }

    if (kind == TokenKind::InterconnectKeyword) {
        auto keyword = consume();
        // TODO: parse implicit data type only
        return allocate<InterconnectPortHeaderSyntax>(direction, keyword, nullptr);
    }

    if (kind == TokenKind::VarKeyword) {
        auto varKeyword = consume();
        return allocate<VariablePortHeaderSyntax>(direction, varKeyword, &parseDataType(/* allowImplicit */ true));
    }

    if (kind == TokenKind::Identifier) {
        // could be a bunch of different things here; scan ahead to see
        if (peek(1).kind == TokenKind::Dot && peek(2).kind == TokenKind::Identifier && peek(3).kind == TokenKind::Identifier) {
            auto name = consume();
            return allocate<InterfacePortHeaderSyntax>(name, parseDotMemberClause());
        }

        DataTypeSyntax* type = nullptr;
        if (!isPlainPortName())
            type = &parseDataType(/* allowImplicit */ false);

        return allocate<VariablePortHeaderSyntax>(direction, Token(), type);
    }

    // assume we have some kind of data type here
    return allocate<VariablePortHeaderSyntax>(direction, Token(), &parseDataType(/* allowImplicit */ true));
}

AnsiPortSyntax& Parser::parseAnsiPort() {
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

        ExpressionSyntax* expr;
        if (!peek(TokenKind::CloseParenthesis))
            expr = &parseExpression();

        return allocate<ExplicitAnsiPortSyntax>(attributes, direction, dot, name, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    auto& header = parsePortHeader(direction);
    auto& declarator = parseVariableDeclarator(/* isFirst */ true);
    return allocate<ImplicitAnsiPortSyntax>(attributes, header, declarator);
}

PortDeclarationSyntax& Parser::parsePortDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    auto& header = parsePortHeader(direction);

    Token semi;
    auto declarators = parseVariableDeclarators(semi);
    return allocate<PortDeclarationSyntax>(attributes, header, declarators, semi);
}

bool Parser::isPlainPortName() {
    int index = 1;
    while (peek(index).kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInPortReference>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
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
    // scan over select expressions until we find out
    int index = 1;
    while (true) {
        kind = peek(index++).kind;
        if (kind == TokenKind::Dot) {
            if (peek(index++).kind != TokenKind::Identifier)
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
        return &parseHierarchyInstantiation(attributes);
    if (isPortDeclaration())
        return &parsePortDeclaration(attributes);
    if (isNetDeclaration())
        return &parseNetDeclaration(attributes);
    if (isVariableDeclaration())
        return &parseVariableDeclaration(attributes);

    switch (peek().kind) {
        case TokenKind::GenerateKeyword: {
            errorIfAttributes(attributes, "a generate region");
            auto keyword = consume();

            // It's definitely not legal to have a generate block here on its own (without an if or for loop)
            // but some simulators seems to accept it and I've found code in the wild that depends on it.
            // We'll parse it here and then issue a diagnostic about how it's not kosher.
            if (peek(TokenKind::BeginKeyword)) {
                // TODO: error
                auto member = &parseGenerateBlock();
                ArrayRef<MemberSyntax*> members { &member, 1 };
                return &allocate<GenerateRegionSyntax>(attributes, keyword, members, expect(TokenKind::EndGenerateKeyword));
            }

            Token endgenerate;
            auto members = parseMemberList<MemberSyntax>(TokenKind::EndGenerateKeyword, endgenerate, [this]() { return parseMember(); });
            return &allocate<GenerateRegionSyntax>(attributes, keyword, members, endgenerate);
        }
        case TokenKind::TimeUnitKeyword:
        case TokenKind::TimePrecisionKeyword:
            errorIfAttributes(attributes, "a time units declaration");
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
            // named assertion label
            // TODO: Don't assume we have an assert here; this could be an accidental label or something
            auto name = consume();
            auto& label = allocate<NamedLabelSyntax>(name, expect(TokenKind::Colon));
            auto& statement = parseAssertionStatement(&label, nullptr);
            switch (statement.kind) {
                case SyntaxKind::ImmediateAssertStatement:
                case SyntaxKind::ImmediateAssumeStatement:
                case SyntaxKind::ImmediateCoverStatement:
                    return &allocate<ImmediateAssertionMemberSyntax>(attributes, statement.as<ImmediateAssertionStatementSyntax>());
                default:
                    return &allocate<ConcurrentAssertionMemberSyntax>(attributes, statement.as<ConcurrentAssertionStatementSyntax>());
            }
        }
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword:
        case TokenKind::RestrictKeyword: {
            auto& statement = parseAssertionStatement(nullptr, nullptr);
            switch (statement.kind) {
                case SyntaxKind::ImmediateAssertStatement:
                case SyntaxKind::ImmediateAssumeStatement:
                case SyntaxKind::ImmediateCoverStatement:
                    return &allocate<ImmediateAssertionMemberSyntax>(attributes, statement.as<ImmediateAssertionStatementSyntax>());
                default:
                    return &allocate<ConcurrentAssertionMemberSyntax>(attributes, statement.as<ConcurrentAssertionStatementSyntax>());
            }
        }
        case TokenKind::AssignKeyword:
            return &parseContinuousAssign(attributes);
        case TokenKind::InitialKeyword: {
            auto keyword = consume();
            return &allocate<ProceduralBlockSyntax>(getProceduralBlockKind(keyword.kind), attributes, keyword, parseStatement());
        }
        case TokenKind::FinalKeyword:
        case TokenKind::AlwaysKeyword:
        case TokenKind::AlwaysCombKeyword:
        case TokenKind::AlwaysFFKeyword:
        case TokenKind::AlwaysLatchKeyword: {
            auto keyword = consume();
            return &allocate<ProceduralBlockSyntax>(getProceduralBlockKind(keyword.kind), attributes, keyword, parseStatement(false));
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
            return &parseFunctionDeclaration(attributes, SyntaxKind::TaskDeclaration, TokenKind::EndTaskKeyword);
        case TokenKind::FunctionKeyword:
            return &parseFunctionDeclaration(attributes, SyntaxKind::FunctionDeclaration, TokenKind::EndFunctionKeyword);
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
            return &allocate<EmptyMemberSyntax>(attributes, nullptr, consume());
        case TokenKind::PropertyKeyword:
        case TokenKind::SequenceKeyword:
            return &parsePropertySequenceDeclaration(attributes);
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
    if (attributes.count())
        return &allocate<EmptyMemberSyntax>(attributes, nullptr, expect(TokenKind::Semicolon));

    // otherwise, we got nothing and should just return null so that our caller will skip and try again.
    return nullptr;
}

template<typename TMember, typename TParseFunc>
ArrayRef<TMember*> Parser::parseMemberList(TokenKind endKind, Token& endToken, TParseFunc&& parseFunc) {
    SmallVectorSized<TMember*, 16> members;
    bool error = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || kind == endKind)
            break;

        auto member = parseFunc();
        if (!member) {
            // couldn't parse anything, skip a token and try again
            auto location = skipToken();
            if (!error) {
                addError(DiagCode::InvalidTokenInMemberList, location);
                error = true;
            }
        }
        else {
            members.append(member);
            error = false;
        }
    }

    endToken = expect(endKind);
    return members.copy(alloc);
}

TimeUnitsDeclarationSyntax& Parser::parseTimeUnitsDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto time = expect(TokenKind::TimeLiteral);

    DividerClauseSyntax* divider = nullptr;
    if (peek(TokenKind::Slash)) {
        auto divide = consume();
        divider = &allocate<DividerClauseSyntax>(divide, expect(TokenKind::TimeLiteral));
    }

    return allocate<TimeUnitsDeclarationSyntax>(attributes, keyword, time, divider, expect(TokenKind::Semicolon));
}

ModportItemSyntax& Parser::parseModportItem() {
    auto name = expect(TokenKind::Identifier);
    auto& ports = parseAnsiPortList(expect(TokenKind::OpenParenthesis));
    return allocate<ModportItemSyntax>(name, ports);
}

ModportDeclarationSyntax& Parser::parseModportDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseSeparatedList<isIdentifierOrComma, isSemicolon>(
        buffer,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedIdentifier,
        [this](bool) -> decltype(auto) { return parseModportItem(); }
    );

    return allocate<ModportDeclarationSyntax>(attributes, keyword, buffer.copy(alloc), semi);
}

FunctionPortSyntax& Parser::parseFunctionPort() {
    auto attributes = parseAttributes();
    auto constKeyword = consumeIf(TokenKind::ConstKeyword);

    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    if (constKeyword && direction.kind != TokenKind::RefKeyword) {
        auto location = direction ? direction.location() : constKeyword.location();
        addError(DiagCode::ConstFunctionPortRequiresRef, location);
    }

    Token varKeyword = consumeIf(TokenKind::VarKeyword);

    // The data type is fully optional; if we see an identifier here we need
    // to disambiguate. Otherwise see if we have a port name or nothing at all.
    DataTypeSyntax* dataType = nullptr;
    if (!peek(TokenKind::Identifier))
        dataType = &parseDataType(/* allowImplicit */ true);
    else if (!isPlainPortName())
        dataType = &parseDataType(/* allowImplicit */ false);

    return allocate<FunctionPortSyntax>(
        attributes,
        constKeyword,
        direction,
        varKeyword,
        dataType,
        parseVariableDeclarator(/* isFirst */ true)
    );
}

FunctionPrototypeSyntax& Parser::parseFunctionPrototype(bool allowTasks) {
    Token keyword;
    if (allowTasks && peek(TokenKind::TaskKeyword)) {
        keyword = consume();
    } else {
        keyword = expect(TokenKind::FunctionKeyword);
    }
    auto lifetime = parseLifetime();

    // check for a return type here
    DataTypeSyntax* returnType = nullptr;
    int index = 0;
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
        if (peek(TokenKind::CloseParenthesis))
            portList = &allocate<FunctionPortListSyntax>(openParen, nullptr, consume());
        else {
            Token closeParen;
            SmallVectorSized<TokenOrSyntax, 8> buffer;
            parseSeparatedList<isPossibleFunctionPort, isEndOfParenList>(
                buffer,
                TokenKind::CloseParenthesis,
                TokenKind::Comma,
                closeParen,
                DiagCode::ExpectedFunctionPort,
                [this](bool) -> decltype(auto) { return parseFunctionPort(); }
            );
            portList = &allocate<FunctionPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
        }
    }

    auto semi = expect(TokenKind::Semicolon);
    return allocate<FunctionPrototypeSyntax>(keyword, lifetime, returnType, name, portList, semi);
}

FunctionDeclarationSyntax& Parser::parseFunctionDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind functionKind, TokenKind endKind) {
    Token end;
    auto& prototype = parseFunctionPrototype();
    auto items = parseBlockItems(endKind, end);
    auto endBlockName = parseNamedBlockClause();

    return allocate<FunctionDeclarationSyntax>(functionKind, attributes, prototype, items, end, endBlockName);
}

GenvarDeclarationSyntax& Parser::parseGenvarDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    Token keyword;
    Token semi;
    ArrayRef<TokenOrSyntax> identifiers = nullptr;

    parseSeparatedList<isIdentifierOrComma, isSemicolon>(
        TokenKind::GenVarKeyword,
        TokenKind::Semicolon,
        TokenKind::Comma,
        keyword,
        identifiers,
        semi,
        DiagCode::ExpectedIdentifier,
        [this](bool) -> decltype(auto) { return allocate<IdentifierNameSyntax>(consume()); }
    );

    return allocate<GenvarDeclarationSyntax>(attributes, keyword, identifiers, semi);
}

LoopGenerateSyntax& Parser::parseLoopGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto genvar = consumeIf(TokenKind::GenVarKeyword);
    auto identifier = expect(TokenKind::Identifier);
    auto equals = expect(TokenKind::Equals);
    auto& initialExpr = parseExpression();
    auto semi1 = expect(TokenKind::Semicolon);
    auto& stopExpr = parseExpression();
    auto semi2 = expect(TokenKind::Semicolon);
    auto& iterationExpr = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    // Make sure that the iteration statement is one of the few allowed by the standard:
    //      genvar_identifier assignment_operator genvar_expression
    // |    inc_or_dec_operator genvar_identifier
    // |    genvar_identifier inc_or_dec_operator

    ExpressionSyntax* iterVarCheck = nullptr;
    switch (iterationExpr.kind) {
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
            iterVarCheck = &iterationExpr.as<BinaryExpressionSyntax>().left;
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            iterVarCheck = &iterationExpr.as<PrefixUnaryExpressionSyntax>().operand;
            break;
        case SyntaxKind::PostincrementExpression:
        case SyntaxKind::PostdecrementExpression:
            iterVarCheck = &iterationExpr.as<PostfixUnaryExpressionSyntax>().operand;
            break;
        default:
            addError(DiagCode::InvalidGenvarIterExpression, iterationExpr.getFirstToken().location())
                << iterationExpr.sourceRange();
            iterationExpr = allocate<BadExpressionSyntax>(iterationExpr);
            break;
    }

    if (iterVarCheck && iterVarCheck->kind != SyntaxKind::IdentifierName) {
        addError(DiagCode::ExpectedGenvarIterVar, iterVarCheck->getFirstToken().location())
            << iterVarCheck->sourceRange();
        iterationExpr = allocate<BadExpressionSyntax>(iterationExpr);
    }

    return allocate<LoopGenerateSyntax>(
        attributes,
        keyword,
        openParen,
        genvar,
        identifier,
        equals,
        initialExpr,
        semi1,
        stopExpr,
        semi2,
        iterationExpr,
        closeParen,
        parseGenerateBlock()
    );
}

IfGenerateSyntax& Parser::parseIfGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& block = parseGenerateBlock();

    ElseClauseSyntax* elseClause = nullptr;
    if (peek(TokenKind::ElseKeyword)) {
        auto elseKeyword = consume();
        elseClause = &allocate<ElseClauseSyntax>(elseKeyword, parseGenerateBlock());
    }

    return allocate<IfGenerateSyntax>(
        attributes,
        keyword,
        openParen,
        condition,
        closeParen,
        block,
        elseClause
    );
}

CaseGenerateSyntax& Parser::parseCaseGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& condition = parseExpression();
    auto closeParen = expect(TokenKind::CloseParenthesis);

    SmallVectorSized<CaseItemSyntax*, 8> itemBuffer;
    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::DefaultKeyword) {
            auto def = consume();
            auto colon = consumeIf(TokenKind::Colon);
            itemBuffer.append(&allocate<DefaultCaseItemSyntax>(def, colon, parseGenerateBlock()));
        }
        else if (isPossibleExpression(kind)) {
            Token colon;
            SmallVectorSized<TokenOrSyntax, 8> buffer;
            parseSeparatedList<isPossibleExpression, isEndOfCaseItem>(
                buffer,
                TokenKind::Colon,
                TokenKind::Comma,
                colon,
                DiagCode::ExpectedExpression,
                [this](bool) -> decltype(auto) { return parseExpression(); }
            );
            itemBuffer.append(&allocate<StandardCaseItemSyntax>(buffer.copy(alloc), colon, parseGenerateBlock()));
        }
        else {
            break;
        }
    }

    auto endcase = expect(TokenKind::EndCaseKeyword);
    return allocate<CaseGenerateSyntax>(
        attributes,
        keyword,
        openParen,
        condition,
        closeParen,
        itemBuffer.copy(alloc),
        endcase
    );
}

MemberSyntax& Parser::parseGenerateBlock() {
    NamedLabelSyntax* label = nullptr;
    if (!peek(TokenKind::BeginKeyword)) {
        if (!peek(TokenKind::Identifier) || peek(1).kind != TokenKind::Colon || peek(2).kind != TokenKind::BeginKeyword) {
            // This is just a single member instead of a block.
            auto member = parseMember();
            if (member)
                return *member;

            // If there was some syntax error that caused parseMember to return null, fabricate an empty
            // member here and let our caller sort it out.
            addError(DiagCode::InvalidTokenInMemberList, peek().location());
            return allocate<EmptyMemberSyntax>(nullptr, nullptr, Token());
        }

        auto name = consume();
        label = &allocate<NamedLabelSyntax>(name, consume());
    }

    auto begin = consume();
    auto beginName = parseNamedBlockClause();

    Token end;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndKeyword, end, [this]() { return parseMember(); });
    auto endName = parseNamedBlockClause();

    return allocate<GenerateBlockSyntax>(
        nullptr, // never any attributes
        label,
        begin,
        beginName,
        members,
        end,
        endName
    );
}

ImplementsClauseSyntax* Parser::parseImplementsClause(TokenKind keywordKind, Token& semi) {
    if (!peek(keywordKind)) {
        semi = expect(TokenKind::Semicolon);
        return nullptr;
    }

    auto implements = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseSeparatedList<isPossibleExpressionOrComma, isSemicolon>(
        buffer,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedInterfaceClassName,
        [this](bool) -> decltype(auto) { return parseName(); }
    );

    return &allocate<ImplementsClauseSyntax>(implements, buffer.copy(alloc));
}

ClassDeclarationSyntax& Parser::parseClassDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, Token virtualOrInterface) {
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
            extendsClause = &allocate<ExtendsClauseSyntax>(extends, baseName, arguments);
        }
        implementsClause = parseImplementsClause(TokenKind::ImplementsKeyword, semi);
    }

    Token endClass;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndClassKeyword, endClass, [this]() { return parseClassMember(); });
    auto endBlockName = parseNamedBlockClause();
    return allocate<ClassDeclarationSyntax>(
        attributes,
        virtualOrInterface,
        classKeyword,
        lifetime,
        name,
        parameterList,
        extendsClause,
        implementsClause,
        semi,
        members,
        endClass,
        endBlockName
    );
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
                return &allocate<ClassPropertyDeclarationSyntax>(attributes, nullptr, parseVariableDeclaration(nullptr));
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
        auto& decl = parseVariableDeclaration(nullptr);
        if (decl.kind == SyntaxKind::ParameterDeclarationStatement)
            errorIfAttributes(attributes, "a class parameter");
        return &allocate<ClassPropertyDeclarationSyntax>(attributes, qualifiers, decl);
    }

    if (kind == TokenKind::TaskKeyword || kind == TokenKind::FunctionKeyword) {
        if (isPureOrExtern)
            return &allocate<ClassMethodPrototypeSyntax>(attributes, qualifiers, parseFunctionPrototype());
        else {
            auto declKind = kind == TokenKind::TaskKeyword ? SyntaxKind::TaskDeclaration : SyntaxKind::FunctionDeclaration;
            auto endKind = kind == TokenKind::TaskKeyword ? TokenKind::EndTaskKeyword : TokenKind::EndFunctionKeyword;
            return &allocate<ClassMethodDeclarationSyntax>(
                attributes,
                qualifiers,
                parseFunctionDeclaration(nullptr, declKind, endKind)
            );
        }
    }

    if (kind == TokenKind::ConstraintKeyword)
        return &parseConstraint(attributes, qualifiers);

    // qualifiers aren't allowed past this point, so return an empty member to hold them
    // TODO: specific error code for this
    // TODO: don't expect semi, just making it missing
    if (qualifiers.count())
        return &allocate<EmptyMemberSyntax>(attributes, qualifiers, expect(TokenKind::Semicolon));

    switch (kind) {
        case TokenKind::ClassKeyword:
            return &parseClassDeclaration(attributes, Token());
        case TokenKind::CoverGroupKeyword:
            return &parseCovergroupDeclaration(attributes);
        case TokenKind::Semicolon:
            errorIfAttributes(attributes, "an empty member");
            return &allocate<EmptyMemberSyntax>(attributes, qualifiers, consume());
        default:
            break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (attributes.count())
        return &allocate<EmptyMemberSyntax>(attributes, qualifiers, expect(TokenKind::Semicolon));

    // otherwise, we got nothing and should just return null so that our caller will skip and try again.
    return nullptr;
}

ContinuousAssignSyntax& Parser::parseContinuousAssign(ArrayRef<AttributeInstanceSyntax*> attributes) {
    // TODO: timing control
    auto assign = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    Token semi;
    parseSeparatedList<isPossibleExpressionOrComma, isSemicolon>(
        buffer,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedVariableAssignment,
        [this](bool) -> decltype(auto) { return parseExpression(); }
    );

    return allocate<ContinuousAssignSyntax>(attributes, assign, buffer.copy(alloc), semi);
}

DefParamAssignmentSyntax& Parser::parseDefParamAssignment() {
    auto& name = parseName();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &allocate<EqualsValueClauseSyntax>(equals, parseMinTypMaxExpression());
    }
    return allocate<DefParamAssignmentSyntax>(name, initializer);
}

DefParamSyntax& Parser::parseDefParam(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto defparam = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    Token semi;
    parseSeparatedList<isPossibleExpressionOrComma, isSemicolon>(
        buffer,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedVariableAssignment,
        [this](bool) -> decltype(auto) { return parseDefParamAssignment(); }
    );

    return allocate<DefParamSyntax>(attributes, defparam, buffer.copy(alloc), semi);
}

CoverageOptionSyntax* Parser::parseCoverageOption(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto token = peek();
    if (token.kind == TokenKind::Identifier) {
        if (token.valueText() == "option" || token.valueText() == "type_option") {
            consume();
            auto dot = expect(TokenKind::Dot);
            auto name = expect(TokenKind::Identifier);
            auto equals = expect(TokenKind::Equals);
            auto& expr = parseExpression();
            return &allocate<CoverageOptionSyntax>(attributes, token, dot, name, equals, expr, expect(TokenKind::Semicolon));
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
        auto& label = allocate<NamedLabelSyntax>(name, consume());
        return parseCoverpoint(attributes, nullptr, &label);
    }

    if (isPossibleDataType(token.kind)) {
        auto& type = parseDataType(/* allowImplicit */ true);
        auto name = expect(TokenKind::Identifier);
        auto& label = allocate<NamedLabelSyntax>(name, expect(TokenKind::Colon));
        return parseCoverpoint(attributes, &type, &label);
    }

    switch (token.kind) {
        case TokenKind::CoverPointKeyword: return parseCoverpoint(attributes, nullptr, nullptr);
        default: break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (attributes.count())
        return &allocate<EmptyMemberSyntax>(attributes, nullptr, expect(TokenKind::Semicolon));

    // otherwise, we got nothing and should just return null so that our caller will skip and try again.
    return nullptr;
}

CoverpointSyntax* Parser::parseCoverpoint(ArrayRef<AttributeInstanceSyntax*> attributes, DataTypeSyntax* type, NamedLabelSyntax* label) {
    // if we have total junk here don't bother trying to fabricate a working tree
    if (attributes.empty() && !type && !label && !peek(TokenKind::CoverPointKeyword))
        return nullptr;

    Token keyword = expect(TokenKind::CoverPointKeyword);
    auto& expr = parseExpression();
    // TODO: handle iff clause separately?

    if (peek(TokenKind::OpenBrace)) {
        auto openBrace = consume();

        Token closeBrace;
        auto members = parseMemberList<MemberSyntax>(TokenKind::CloseBrace, closeBrace, [this]() { return parseCoverpointMember(); });
        return &allocate<CoverpointSyntax>(
            attributes,
            type,
            label,
            keyword,
            expr,
            openBrace,
            members,
            closeBrace,
            Token()
        );
    }

    // no brace, so this is an empty list, expect a semicolon
    return &allocate<CoverpointSyntax>(
        attributes,
        type,
        label,
        keyword,
        expr,
        Token(),
        nullptr,
        Token(),
        expect(TokenKind::Semicolon)
    );
}

WithClauseSyntax* Parser::parseWithClause() {
    if (!peek(TokenKind::WithKeyword))
        return nullptr;

    auto with = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    return &allocate<WithClauseSyntax>(with, openParen, expr, expect(TokenKind::CloseParenthesis));
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
        errorIfAttributes(attributes, "an empty item");
        return &allocate<EmptyMemberSyntax>(attributes, nullptr, consume());
    }

    // error out if we have total junk here
    if (!wildcard && !bins && attributes.empty())
        return nullptr;

    Token name = expect(TokenKind::Identifier);

    ElementSelectSyntax* selector = nullptr;
    if (peek(TokenKind::OpenBracket))
        selector = &parseElementSelect();

    // bunch of different kinds of initializers here
    CoverageBinInitializerSyntax* initializer;
    Token equals = expect(TokenKind::Equals);

    switch (peek().kind) {
        case TokenKind::OpenBrace: {
            auto& ranges = parseOpenRangeList();
            auto with = parseWithClause();
            initializer = &allocate<RangeCoverageBinInitializerSyntax>(ranges, with);
            break;
        }
        case TokenKind::DefaultKeyword: {
            auto defaultKeyword = consume();
            auto sequenceKeyword = consumeIf(TokenKind::SequenceKeyword);
            initializer = &allocate<DefaultCoverageBinInitializerSyntax>(defaultKeyword, sequenceKeyword);
            break;
        }
        // TODO: trans_list
        default: {
            auto& expr = parseExpression();
            auto with = parseWithClause();
            initializer = &allocate<ExpressionCoverageBinInitializerSyntax>(expr, with);
            break;
        }
    }

    IffClauseSyntax* iffClause = nullptr;
    if (peek(TokenKind::IffKeyword)) {
        auto iff = consume();
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpression();
        iffClause = &allocate<IffClauseSyntax>(iff, openParen, expr, expect(TokenKind::CloseParenthesis));
    }

    return &allocate<CoverageBinsSyntax>(
        attributes,
        wildcard,
        bins,
        name,
        selector,
        equals,
        *initializer,
        iffClause,
        expect(TokenKind::Semicolon)
    );
}

BlockEventExpressionSyntax& Parser::parseBlockEventExpression() {
    Token keyword;
    switch (peek().kind) {
        case TokenKind::BeginKeyword:
        case TokenKind::EndKeyword:
            keyword = consume();
            break;
        default:
            // TODO: better error message here? begin or end expected
            keyword = expect(TokenKind::BeginKeyword);
            break;
    }

    auto& name = parseName();
    auto& left = allocate<PrimaryBlockEventExpressionSyntax>(keyword, name);

    if (peek(TokenKind::OrKeyword)) {
        auto op = consume();
        auto& right = parseBlockEventExpression();
        return allocate<BinaryBlockEventExpressionSyntax>(left, op, right);
    }
    return left;
}

CovergroupDeclarationSyntax& Parser::parseCovergroupDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);

    AnsiPortListSyntax* portList = nullptr;
    if (peek(TokenKind::OpenParenthesis))
        portList = &parseAnsiPortList(consume());

    SyntaxNode* event = nullptr;
    switch (peek().kind) {
        case TokenKind::At: {
            auto at = consume();
            event = &allocate<EventControlWithExpressionSyntax>(at, parseEventExpression());
            break;
        }
        case TokenKind::DoubleAt:
            event = &parseBlockEventExpression();
            break;
        case TokenKind::WithKeyword: {
            auto with = consume();
            auto function = expect(TokenKind::FunctionKeyword);
            auto sample = expect(TokenKind::Identifier); // TODO: make sure this is "sample" (maybe in the binder?)
            auto& samplePortList = parseAnsiPortList(expect(TokenKind::OpenParenthesis));
            event = &allocate<WithFunctionSampleSyntax>(with, function, sample, samplePortList);
            break;
        }
        default:
            break;
    }

    auto semi = expect(TokenKind::Semicolon);

    Token endGroup;
    auto members = parseMemberList<MemberSyntax>(TokenKind::EndGroupKeyword, endGroup, [this]() { return parseCoverageMember(); });
    auto endBlockName = parseNamedBlockClause();
    return allocate<CovergroupDeclarationSyntax>(
        attributes,
        keyword,
        name,
        portList,
        event,
        semi,
        members,
        endGroup,
        endBlockName
    );
}

MemberSyntax& Parser::parseConstraint(ArrayRef<AttributeInstanceSyntax*> attributes, ArrayRef<Token> qualifiers) {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    if (peek(TokenKind::Semicolon)) {
        // this is just a prototype
        return allocate<ConstraintPrototypeSyntax>(attributes, qualifiers, keyword, name, consume());
    }
    return allocate<ConstraintDeclarationSyntax>(attributes, qualifiers, keyword, name, parseConstraintBlock());
}

ConstraintBlockSyntax& Parser::parseConstraintBlock() {
    Token closeBrace;
    auto openBrace = expect(TokenKind::OpenBrace);
    auto members = parseMemberList<ConstraintItemSyntax>(TokenKind::CloseBrace, closeBrace, [this]() { return &parseConstraintItem(false); });
    return allocate<ConstraintBlockSyntax>(openBrace, members, closeBrace);
}

ExpressionSyntax& Parser::parseExpressionOrDist() {
    auto& expr = parseExpression();
    if (!peek(TokenKind::DistKeyword))
        return expr;

    auto& dist = parseDistConstraintList();
    return allocate<ExpressionOrDistSyntax>(expr, dist);
}

ConstraintItemSyntax& Parser::parseConstraintItem(bool allowBlock) {
    switch (peek().kind) {
        case TokenKind::SolveKeyword: {
            auto solve = consume();
            Token before;
            SmallVectorSized<TokenOrSyntax, 4> beforeBuffer;
            parseSeparatedList<isPossibleExpression, isBeforeOrSemicolon>(
                beforeBuffer,
                TokenKind::BeforeKeyword,
                TokenKind::Comma,
                before,
                DiagCode::ExpectedExpression,
                [this](bool) -> decltype(auto) { return parsePrimaryExpression(); }
            );
            Token semi;
            SmallVectorSized<TokenOrSyntax, 4> afterBuffer;
            parseSeparatedList<isPossibleExpression, isSemicolon>(
                afterBuffer,
                TokenKind::Semicolon,
                TokenKind::Comma,
                semi,
                DiagCode::ExpectedExpression,
                [this](bool) -> decltype(auto) { return parsePrimaryExpression(); }
            );
            return allocate<SolveBeforeConstraintSyntax>(solve, beforeBuffer.copy(alloc), before, afterBuffer.copy(alloc), semi);
        }
        case TokenKind::DisableKeyword: {
            auto disable = consume();
            auto soft = expect(TokenKind::SoftKeyword);
            auto& name = parseName();
            return allocate<DisableConstraintSyntax>(disable, soft, name, expect(TokenKind::Semicolon));
        }
        case TokenKind::ForeachKeyword: {
            auto keyword = consume();
            auto& vars = parseForeachLoopVariables();
            return allocate<LoopConstraintSyntax>(keyword, vars, parseConstraintItem(true));
        }
        case TokenKind::IfKeyword: {
            auto ifKeyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& constraints = parseConstraintItem(true);

            ElseConstraintClauseSyntax* elseClause = nullptr;
            if (peek(TokenKind::ElseKeyword)) {
                auto elseKeyword = consume();
                elseClause = &allocate<ElseConstraintClauseSyntax>(elseKeyword, parseConstraintItem(true));
            }
            return allocate<ConditionalConstraintSyntax>(ifKeyword, openParen, condition, closeParen, constraints, elseClause);
        }
        case TokenKind::UniqueKeyword: {
            auto keyword = consume();
            auto& list = parseOpenRangeList();
            return allocate<UniquenessConstraintSyntax>(keyword, list, expect(TokenKind::Semicolon));
        }
        case TokenKind::SoftKeyword: {
            auto soft = consume();
            auto& exprOrDist = parseExpressionOrDist();
            return allocate<ExpressionConstraintSyntax>(soft, exprOrDist, expect(TokenKind::Semicolon));
        }
        case TokenKind::OpenBrace: {
            // Ambiguity here: an open brace could either be the start of a constraint block
            // or the start of a concatenation expression. Descend into the expression until
            // we can find out for sure one way or the other.
            if (allowBlock) {
                int index = 1;
                if (!scanTypePart<isNotInConcatenationExpr>(index, TokenKind::OpenBrace, TokenKind::CloseBrace))
                    return parseConstraintBlock();
            }
            break;
        }
        default:
            break;
    }

    // at this point we either have an expression with optional distribution or
    // we have an implication constraint
    auto& expr = parseExpression();
    if (peek(TokenKind::MinusArrow)) {
        auto arrow = consume();
        return allocate<ImplicationConstraintSyntax>(expr, arrow, parseConstraintItem(true));
    }

    if (peek(TokenKind::DistKeyword)) {
        auto& dist = parseDistConstraintList();
        expr = allocate<ExpressionOrDistSyntax>(expr, dist);
    }

    return allocate<ExpressionConstraintSyntax>(Token(), expr, expect(TokenKind::Semicolon));
}

DistConstraintListSyntax& Parser::parseDistConstraintList() {
    auto dist = consume();

    Token openBrace;
    Token closeBrace;
    ArrayRef<TokenOrSyntax> list;

    parseSeparatedList<isPossibleOpenRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace,
        TokenKind::CloseBrace,
        TokenKind::Comma,
        openBrace,
        list,
        closeBrace,
        DiagCode::ExpectedDistItem,
        [this](bool) -> decltype(auto) { return parseDistItem(); }
    );

    return allocate<DistConstraintListSyntax>(dist, openBrace, list, closeBrace);
}

DistItemSyntax& Parser::parseDistItem() {
    auto& range = parseOpenRangeElement();

    DistWeightSyntax* weight = nullptr;
    if (peek(TokenKind::ColonEquals) || peek(TokenKind::ColonSlash)) {
        auto op = consume();
        weight = &allocate<DistWeightSyntax>(op, parseExpression());
    }

    return allocate<DistItemSyntax>(range, weight);
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
            specifier = &allocate<WildcardDimensionSpecifierSyntax>(consume());
            break;
        case TokenKind::Dollar: {
            auto dollar = consume();

            ColonExpressionClauseSyntax* colonExpressionClause = nullptr;
            if (peek(TokenKind::Colon)) {
                auto colon = consume();
                colonExpressionClause = &allocate<ColonExpressionClauseSyntax>(colon, parseExpression());
            }
            specifier = &allocate<QueueDimensionSpecifierSyntax>(dollar, colonExpressionClause);
            break;
        }
        default: {
            auto selector = parseElementSelector();
            ASSERT(selector);
            specifier = &allocate<RangeDimensionSpecifierSyntax>(*selector);
            break;
        }
    }

    auto closeBracket = expect(TokenKind::CloseBracket);
    return &allocate<VariableDimensionSyntax>(openBracket, specifier, closeBracket);
}

ArrayRef<VariableDimensionSyntax*> Parser::parseDimensionList() {
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
        return &allocate<DotMemberClauseSyntax>(dot, expect(TokenKind::Identifier));
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
        closeBrace = Token::createMissing(alloc, TokenKind::CloseBrace, openBrace.location());
    else {
        auto kind = peek().kind;
        while (kind != TokenKind::CloseBrace && kind != TokenKind::EndOfFile) {
            auto attributes = parseAttributes();

            Token randomQualifier;
            switch (peek().kind) {
                case TokenKind::RandKeyword:
                case TokenKind::RandCKeyword:
                    randomQualifier = consume();
                default:
                    break;
            }

            auto& type = parseDataType(/* allowImplicit */ false);

            Token semi;
            auto declarators = parseVariableDeclarators(semi);

            buffer.append(&allocate<StructUnionMemberSyntax>(attributes, randomQualifier, type, declarators, semi));
            kind = peek().kind;
        }
        closeBrace = expect(TokenKind::CloseBrace);
    }

    return allocate<StructUnionTypeSyntax>(
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

EnumTypeSyntax& Parser::parseEnum() {
    auto keyword = consume();

    DataTypeSyntax* baseType = nullptr;
    if (!peek(TokenKind::OpenBrace))
        baseType = &parseDataType(/* allowImplicit */ false);

    auto openBrace = expect(TokenKind::OpenBrace);

    Token closeBrace;
    ArrayRef<TokenOrSyntax> declarators = nullptr;
    if (openBrace.isMissing())
        closeBrace = Token::createMissing(alloc, TokenKind::CloseBrace, openBrace.location());
    else
        declarators = parseVariableDeclarators<isCloseBrace>(TokenKind::CloseBrace, closeBrace);

    return allocate<EnumTypeSyntax>(keyword, baseType, openBrace, declarators, closeBrace, parseDimensionList());
}

DataTypeSyntax& Parser::parseDataType(bool allowImplicit) {
    auto kind = peek().kind;
    auto type = getIntegerType(kind);
    if (type != SyntaxKind::Unknown) {
        auto keyword = consume();
        auto signing = parseSigning();
        return allocate<IntegerTypeSyntax>(type, keyword, signing, parseDimensionList());
    }

    type = getKeywordType(kind);
    if (type != SyntaxKind::Unknown)
        return allocate<KeywordTypeSyntax>(type, consume());

    switch (kind) {
        case TokenKind::StructKeyword: return parseStructUnion(SyntaxKind::StructType);
        case TokenKind::UnionKeyword: return parseStructUnion(SyntaxKind::UnionType);
        case TokenKind::EnumKeyword: return parseEnum();
        case TokenKind::VirtualKeyword: {
            auto virtualKeyword = consume();
            auto interfaceKeyword = consumeIf(TokenKind::InterfaceKeyword);
            auto name = expect(TokenKind::Identifier);
            auto parameters = parseParameterValueAssignment();
            return allocate<VirtualInterfaceTypeSyntax>(virtualKeyword, interfaceKeyword, name, parameters, parseDotMemberClause());
        }
        case TokenKind::UnitSystemName:
            return allocate<NamedTypeSyntax>(parseName());
        case TokenKind::TypeKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseExpression();
            return allocate<TypeReferenceSyntax>(keyword, openParen, expr, expect(TokenKind::CloseParenthesis));
        }
        default:
            break;
    }

    if (kind == TokenKind::Identifier) {
        if (!allowImplicit)
            return allocate<NamedTypeSyntax>(parseName());
        else {
            // If we're allowed to have an implicit type here, it means there's a chance this
            // identifier is actually the name of something else (like a declaration) and that the
            // type should be implicit. Check if there's another identifier right after us
            // before deciding which one we're looking at.
            int index = 0;
            if (scanQualifiedName(index) && scanDimensionList(index) && peek(index).kind == TokenKind::Identifier)
                return allocate<NamedTypeSyntax>(parseName());
            return allocate<ImplicitTypeSyntax>(Token(), nullptr);
        }
    }

    auto signing = parseSigning();
    auto dimensions = parseDimensionList();

    if (!allowImplicit)
        addError(DiagCode::ImplicitNotAllowed, peek().location());

    return allocate<ImplicitTypeSyntax>(signing, dimensions);
}

MemberSyntax& Parser::parseNetDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
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
    auto declarators = parseVariableDeclarators(semi);

    return allocate<NetDeclarationSyntax>(attributes, netType, strength, expansionHint, type, declarators, semi);
}

MemberSyntax& Parser::parseVariableDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    if (peek(TokenKind::TypedefKeyword)) {
        auto typedefKeyword = consume();
        switch (peek().kind) {
            case TokenKind::EnumKeyword:
            case TokenKind::StructKeyword:
            case TokenKind::UnionKeyword:
            case TokenKind::ClassKeyword:
                if (peek(1).kind == TokenKind::Identifier && peek(2).kind == TokenKind::Semicolon) {
                    auto keyword = consume();
                    auto name = consume();
                    return allocate<TypedefKeywordDeclarationSyntax>(
                        attributes,
                        typedefKeyword,
                        keyword,
                        name,
                        consume());
                }
                break;
            case TokenKind::InterfaceKeyword: {
                auto interfaceKeyword = consume();
                auto classKeyword = expect(TokenKind::ClassKeyword);
                auto name = expect(TokenKind::Identifier);
                return allocate<TypedefInterfaceClassDeclarationSyntax>(
                    attributes,
                    typedefKeyword,
                    interfaceKeyword,
                    classKeyword,
                    name,
                    expect(TokenKind::Semicolon));
            }
            case TokenKind::Identifier:
                if (peek(1).kind == TokenKind::Semicolon) {
                    auto name = consume();
                    return allocate<TypedefKeywordDeclarationSyntax>(
                        attributes,
                        typedefKeyword,
                        Token(),
                        name,
                        consume());
                }
                break;
            default:
                break;
        }
        auto& type = parseDataType(/* allowImplicit */ false);
        auto name = expect(TokenKind::Identifier);
        auto dims = parseDimensionList();
        return allocate<TypedefDeclarationSyntax>(
            attributes,
            typedefKeyword,
            type,
            name,
            dims,
            expect(TokenKind::Semicolon));
    }

    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword)) {
        Token semi;
        auto keyword = consume();
        auto& type = parseDataType(/* allowImplicit */ true);
        auto& parameter = allocate<ParameterDeclarationSyntax>(keyword, type, parseVariableDeclarators(semi));
        return allocate<ParameterDeclarationStatementSyntax>(attributes, parameter, semi);
    }

    if (peek(TokenKind::LetKeyword)) {
        auto let = consume();
        auto identifier = expect(TokenKind::Identifier);
        auto portList = parseAssertionItemPortList(TokenKind::LetKeyword);
        auto& initializer = allocate<EqualsValueClauseSyntax>(expect(TokenKind::Equals), parseExpression());
        return allocate<LetDeclarationSyntax>(attributes, let, identifier, portList, initializer, expect(TokenKind::Semicolon));
    }

    // TODO: other kinds of declarations besides data
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
    auto declarators = parseVariableDeclarators(semi);

    return allocate<DataDeclarationSyntax>(attributes, modifiers.copy(alloc), dataType, declarators, semi);
}

VariableDeclaratorSyntax& Parser::parseVariableDeclarator(bool isFirst) {
    auto name = expect(TokenKind::Identifier);

    // Give a better error message for cases like:
    // X x = 1, Y y = 2;
    // The second identifier would be treated as a variable name, which is confusing
    if (!isFirst && peek(TokenKind::Identifier))
        addError(DiagCode::MultipleTypesInDeclaration, peek().location());

    auto dimensions = parseDimensionList();

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &allocate<EqualsValueClauseSyntax>(equals, parseMinTypMaxExpression());
    }

    return allocate<VariableDeclaratorSyntax>(name, dimensions, initializer);
}

ArrayRef<TokenOrSyntax> Parser::parseOneVariableDeclarator() {
    SmallVectorSized<TokenOrSyntax, 2> buffer;
    buffer.append(&parseVariableDeclarator(/* isFirst */ true));
    return buffer.copy(alloc);
}

template<bool(*IsEnd)(TokenKind)>
ArrayRef<TokenOrSyntax> Parser::parseVariableDeclarators(TokenKind endKind, Token& end) {
    SmallVectorSized<TokenOrSyntax, 4> buffer;
    parseSeparatedList<isIdentifierOrComma, IsEnd>(
        buffer,
        endKind,
        TokenKind::Comma,
        end,
        DiagCode::ExpectedVariableDeclarator,
        [this](bool first) -> decltype(auto) { return parseVariableDeclarator(first); }
    );

    return buffer.copy(alloc);
}

ArrayRef<TokenOrSyntax> Parser::parseVariableDeclarators(Token& semi) {
    return parseVariableDeclarators<isSemicolon>(TokenKind::Semicolon, semi);
}

ArrayRef<AttributeInstanceSyntax*> Parser::parseAttributes() {
    SmallVectorSized<AttributeInstanceSyntax*, 4> buffer;
    while (peek(TokenKind::OpenParenthesisStar)) {
        Token openParen;
        Token closeParen;
        ArrayRef<TokenOrSyntax> list;

        parseSeparatedList<isIdentifierOrComma, isEndOfAttribute>(
            TokenKind::OpenParenthesisStar,
            TokenKind::StarCloseParenthesis,
            TokenKind::Comma,
            openParen,
            list,
            closeParen,
            DiagCode::ExpectedAttribute,
            [this](bool) -> decltype(auto) { return parseAttributeSpec(); }
        );

        buffer.append(&allocate<AttributeInstanceSyntax>(openParen, list, closeParen));
    }
    return buffer.copy(alloc);
}

AttributeSpecSyntax& Parser::parseAttributeSpec() {
    auto name = expect(TokenKind::Identifier);

    EqualsValueClauseSyntax* initializer = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        initializer = &allocate<EqualsValueClauseSyntax>(equals, parseExpression());
    }

    return allocate<AttributeSpecSyntax>(name, initializer);
}

ArrayRef<PackageImportDeclarationSyntax*> Parser::parsePackageImports() {
    SmallVectorSized<PackageImportDeclarationSyntax*, 4> buffer;
    while (peek(TokenKind::ImportKeyword))
        buffer.append(&parseImportDeclaration(nullptr));
    return buffer.copy(alloc);
}

PackageImportDeclarationSyntax& Parser::parseImportDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 4> items;
    parseSeparatedList<isIdentifierOrComma, isSemicolon>(
        items,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedPackageImport,
        [this](bool) -> decltype(auto) { return parsePackageImportItem(); }
    );

    return allocate<PackageImportDeclarationSyntax>(attributes, keyword, items.copy(alloc), semi);
}

PackageImportItemSyntax& Parser::parsePackageImportItem() {
    auto package = expect(TokenKind::Identifier);
    auto doubleColon = expect(TokenKind::DoubleColon);

    Token item;
    if (peek(TokenKind::Star))
        item = consume();
    else
        item = expect(TokenKind::Identifier);

    return allocate<PackageImportItemSyntax>(package, doubleColon, item);
}

DPIImportExportSyntax& Parser::parseDPIImportExport(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto keyword = consume();
    auto stringLiteral = expect(TokenKind::StringLiteral);
    if (stringLiteral.valueText() != "DPI-C" && stringLiteral.valueText() != "DPI") {
        addError(DiagCode::ExpectedDPISpecString, stringLiteral.location());
    }
    Token property, name, equals;
    if (keyword.kind == TokenKind::ImportKeyword && (peek(TokenKind::ContextKeyword) || peek(TokenKind::PureKeyword))) {
        property = consume();
    }
    if (peek(TokenKind::Identifier)) {
        name = consume();
        equals = expect(TokenKind::Equals);
    }
    auto& method = parseFunctionPrototype(property.kind != TokenKind::PureKeyword);
    return allocate<DPIImportExportSyntax>(attributes, keyword, stringLiteral, property, name, equals, method);
}

AssertionItemPortListSyntax* Parser::parseAssertionItemPortList(TokenKind declarationKind) {
    if (!peek(TokenKind::OpenParenthesis) || (declarationKind != TokenKind::PropertyKeyword && declarationKind != TokenKind::SequenceKeyword && declarationKind != TokenKind::LetKeyword))
        return nullptr;

    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 4> buffer;
    Token closeParen;

    parseSeparatedList<isPossiblePropertyPortItem, isEndOfParenList>(
        buffer,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        closeParen,
        DiagCode::ExpectedAssertionItemPort,
        [this, declarationKind](bool) -> decltype(auto) {
            auto attributes = parseAttributes();
            Token local;
            Token direction;
            if (declarationKind == TokenKind::PropertyKeyword || declarationKind == TokenKind::SequenceKeyword) {
                local = consumeIf(TokenKind::LocalKeyword);
                if (local && (peek(TokenKind::InputKeyword) || (declarationKind == TokenKind::SequenceKeyword && (peek(TokenKind::OutputKeyword) || peek(TokenKind::InOutKeyword))))) {
                    direction = consume();
                }
            }
            DataTypeSyntax* type;
            switch(peek().kind) {
                case TokenKind::PropertyKeyword:
                    if (declarationKind != TokenKind::PropertyKeyword) {
                        type = &parseDataType(true);
                        break;
                    }
                    type = &allocate<KeywordTypeSyntax>(SyntaxKind::PropertyType, consume());
                    break;
                case TokenKind::SequenceKeyword:
                    if (declarationKind == TokenKind::LetKeyword) {
                        type = &parseDataType(true);
                        break;
                    }
                    type = &allocate<KeywordTypeSyntax>(SyntaxKind::SequenceType, consume());
                    break;
                case TokenKind::UntypedKeyword:
                    type = &allocate<KeywordTypeSyntax>(SyntaxKind::Untyped, consume());
                    break;
                default:
                    type = &parseDataType(true);
                    break;
            }
            ASSERT(type);
            auto& declarator = parseVariableDeclarator(true);
            return allocate<AssertionItemPortSyntax>(attributes, local, direction, *type, declarator);
        }
    );

    return &allocate<AssertionItemPortListSyntax>(openParen, buffer.copy(alloc), closeParen);
}

PropertySequenceDeclarationSyntax& Parser::parsePropertySequenceDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto start = consume();
    auto name = expect(TokenKind::Identifier);
    auto portList = parseAssertionItemPortList(start.kind);

    auto semi = expect(TokenKind::Semicolon);
    SmallVectorSized<DataDeclarationSyntax*, 4> declarations;
    while(peek(TokenKind::VarKeyword) || isPossibleDataType(peek().kind)) {
        DataTypeSyntax* type;
        if (peek(TokenKind::VarKeyword))
            type = &allocate<VarDataTypeSyntax>(consume(), parseDataType(true));
        else
            type = &parseDataType(false);

        Token semi2;
        auto variableDeclarators = parseVariableDeclarators(semi2);
        declarations.append(&allocate<DataDeclarationSyntax>(nullptr, nullptr, *type, variableDeclarators, semi2));
    }

    PropertySpecSyntax* spec = nullptr;
    ExpressionSyntax* expr = nullptr;
    Token optSemi, end;
    if (start.kind == TokenKind::PropertyKeyword) {
        spec = &parsePropertySpec();
        optSemi = consumeIf(TokenKind::Semicolon);
        end = expect(TokenKind::EndPropertyKeyword);
    }
    else {
        // TODO: Parse all sequence expressions
        expr = &parseExpression();
        optSemi = consumeIf(TokenKind::Semicolon);
        end = expect(TokenKind::EndSequenceKeyword);
    }
    auto blockName = parseNamedBlockClause();
    return allocate<PropertySequenceDeclarationSyntax>(attributes, start, name, portList, semi, declarations.copy(alloc), spec, expr, optSemi, end, blockName);
}

ParameterDeclarationSyntax& Parser::parseParameterPort() {
    if (peek(TokenKind::ParameterKeyword) || peek(TokenKind::LocalParamKeyword)) {
        auto keyword = consume();
        auto& type = parseDataType(/* allowImplicit */ true);
        return allocate<ParameterDeclarationSyntax>(keyword, type, parseOneVariableDeclarator());
    }

    // this is a normal parameter without the actual parameter keyword (stupid implicit nonsense)
    auto& type = parseDataType(/* allowImplicit */ true);
    return allocate<ParameterDeclarationSyntax>(Token(), type, parseOneVariableDeclarator());
}

ClockingSkewSyntax* Parser::parseClockingSkew() {
    Token edge, hash;
    ExpressionSyntax* value = nullptr;
    if (peek(TokenKind::EdgeKeyword)|| peek(TokenKind::PosEdgeKeyword) || peek(TokenKind::NegEdgeKeyword))
        edge = consume();

    if (peek(TokenKind::Hash)) {
        hash = consume();
        switch(peek().kind) {
            case TokenKind::OpenParenthesis: {
                auto openParen = consume();
                auto& innerExpr = parseMinTypMaxExpression();
                auto closeParen = expect(TokenKind::CloseParenthesis);
                value = &allocate<ParenthesizedExpressionSyntax>(openParen, innerExpr, closeParen);
                break;
            }
            case TokenKind::IntegerLiteral:
            case TokenKind::RealLiteral:
            case TokenKind::TimeLiteral:
            case TokenKind::OneStep: {
                auto literal = consume();
                value = &allocate<LiteralExpressionSyntax>(getLiteralExpression(literal.kind), literal);
                break;
            }
            default:
                value = &allocate<IdentifierNameSyntax>(expect(TokenKind::Identifier));
                break;
        }
    }

    if (!edge && !hash)
        return nullptr;
    return &allocate<ClockingSkewSyntax>(edge, hash, value);
}

ClockingDeclarationSyntax& Parser::parseClockingDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes) {
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
            event = &allocate<ParenthesizedEventExpressionSyntax>(openParen, innerExpr, closeParen);
        }
        else {
            eventIdentifier = expect(TokenKind::Identifier);
        }
    }

    Token semi = expect(TokenKind::Semicolon);
    SmallVectorSized<ClockingItemSyntax*, 4> buffer;
    SmallVectorSized<Token, 4> skipped;
    bool error = false;

    if (globalOrDefault.kind != TokenKind::GlobalKeyword) {
        while(!isEndKeyword(peek().kind) && !peek(TokenKind::EndOfFile)) {
            Token defaultKeyword, inputKeyword, outputKeyword;
            ClockingDirectionSyntax* direction = nullptr;
            ClockingSkewSyntax* inputSkew = nullptr, *outputSkew = nullptr;
            MemberSyntax* declaration = nullptr;

            switch(peek().kind) {
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
                    direction = &allocate<ClockingDirectionSyntax>(inputKeyword, inputSkew, outputKeyword, outputSkew, Token());
                    break;
                case TokenKind::InOutKeyword:
                    direction = &allocate<ClockingDirectionSyntax>(Token(), nullptr, Token(), nullptr, consume());
                    break;
                default:
                    declaration = parseMember();
                    break;
            }

            if (!declaration && !defaultKeyword && !direction) {
                auto token = consume();
                skipped.append(token);
                if (!error) {
                    addError(DiagCode::ExpectedClockingSkew, peek().location());
                    error = true;
                }
                continue;
            }

            Token semi;
            SmallVectorSized<TokenOrSyntax, 4> assignments;
            if (!declaration && !defaultKeyword) {
                parseSeparatedList<isIdentifierOrComma, isSemicolon>(
                    assignments,
                    TokenKind::Semicolon,
                    TokenKind::Comma,
                    semi,
                    DiagCode::ExpectedIdentifier,
                    [this](bool) -> decltype(auto) { return parseAttributeSpec(); }
                );
            }
            else if (!declaration) {
                semi = expect(TokenKind::Semicolon);
            }

            error = false;
            buffer.append(&allocate<ClockingItemSyntax>(defaultKeyword, direction, assignments.copy(alloc), semi, declaration));
        }
    }

    Token endClocking = expect(TokenKind::EndClockingKeyword);
    NamedBlockClauseSyntax* endBlockName = parseNamedBlockClause();
    return allocate<ClockingDeclarationSyntax>(attributes, globalOrDefault, clocking, blockName, at, event, eventIdentifier, semi, buffer.copy(alloc), endClocking, endBlockName);
}

HierarchyInstantiationSyntax& Parser::parseHierarchyInstantiation(ArrayRef<AttributeInstanceSyntax*> attributes) {
    auto type = expect(TokenKind::Identifier);
    auto parameters = parseParameterValueAssignment();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> items;
    parseSeparatedList<isIdentifierOrComma, isSemicolon>(
        items,
        TokenKind::Semicolon,
        TokenKind::Comma,
        semi,
        DiagCode::ExpectedHierarchicalInstantiation,
        [this](bool) -> decltype(auto) { return parseHierarchicalInstance(); }
    );

    return allocate<HierarchyInstantiationSyntax>(attributes, type, parameters, items.copy(alloc), semi);
}

HierarchicalInstanceSyntax& Parser::parseHierarchicalInstance() {
    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    Token openParen;
    Token closeParen;
    ArrayRef<TokenOrSyntax> items = nullptr;

    parseSeparatedList<isPossiblePortConnection, isEndOfParenList>(
        TokenKind::OpenParenthesis,
        TokenKind::CloseParenthesis,
        TokenKind::Comma,
        openParen,
        items,
        closeParen,
        DiagCode::ExpectedPortConnection,
        [this](bool) -> decltype(auto) { return parsePortConnection(); }
    );

    return allocate<HierarchicalInstanceSyntax>(name, dimensions, openParen, items, closeParen);
}

PortConnectionSyntax& Parser::parsePortConnection() {
    auto attributes = parseAttributes();

    if (peek(TokenKind::DotStar))
        return allocate<WildcardPortConnectionSyntax>(attributes, consume());

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
        return allocate<NamedPortConnectionSyntax>(attributes, dot, name, openParen, expr, closeParen);
    }
    return allocate<OrderedPortConnectionSyntax>(attributes, parseExpression());
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
    int index = 0;
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
        case TokenKind::BindKeyword:
        case TokenKind::LetKeyword:
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
    int index = 0;
    if (peek(index++).kind != TokenKind::Identifier)
        return false;

    // skip over optional parameter value assignment
    if (peek(index).kind == TokenKind::Hash) {
        if (peek(++index).kind != TokenKind::OpenParenthesis)
            return false;
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis, TokenKind::CloseParenthesis))
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

bool Parser::scanDimensionList(int& index) {
    while (peek(index).kind == TokenKind::OpenBracket) {
        index++;
        if (!scanTypePart<isNotInType>(index, TokenKind::OpenBracket, TokenKind::CloseBracket))
            return false;
    }
    return true;
}

bool Parser::scanQualifiedName(int& index) {
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
            if (!scanTypePart<isNotInType>(index, TokenKind::OpenParenthesis, TokenKind::CloseParenthesis))
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

void Parser::errorIfAttributes(ArrayRef<AttributeInstanceSyntax*> attributes, const char* msg) {
    if (!attributes.empty())
        addError(DiagCode::AttributesNotSupported, peek().location()) << StringRef(msg, (uint32_t)strlen(msg));
}

void Parser::throwIfTooDeep() {
    if (depth > MaxDepth)
        throw std::runtime_error("Language constructs nested too deep");
}

}
