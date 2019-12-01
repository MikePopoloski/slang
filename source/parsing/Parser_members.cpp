//------------------------------------------------------------------------------
// Parser_members.cpp
// Member-related parsing methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

namespace slang {

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

ModuleDeclarationSyntax& Parser::parseModule() {
    return parseModule(parseAttributes());
}

ModuleDeclarationSyntax& Parser::parseModule(AttrList attributes) {
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

TimeUnitsDeclarationSyntax& Parser::parseTimeUnitsDeclaration(AttrList attributes) {
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

MemberSyntax& Parser::parseModportSubroutinePortList(AttrList attributes) {
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

ModportDeclarationSyntax& Parser::parseModportDeclaration(AttrList attributes) {
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
        dataType = &parseDataType(TypeOptions::AllowImplicit);
    else if (!isPlainPortName())
        dataType = &parseDataType();

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
        returnType = &parseDataType(TypeOptions::AllowImplicit | TypeOptions::AllowVoid);
    else {
        auto next = peek(index);
        if (next.kind != TokenKind::Semicolon && next.kind != TokenKind::OpenParenthesis)
            returnType = &parseDataType(TypeOptions::AllowImplicit | TypeOptions::AllowVoid);
        else
            returnType = &factory.implicitType(Token(), nullptr);
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

    return factory.functionPrototype(keyword, lifetime, *returnType, name, portList);
}

FunctionDeclarationSyntax& Parser::parseFunctionDeclaration(AttrList attributes,
                                                            SyntaxKind functionKind,
                                                            TokenKind endKind) {
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

GenvarDeclarationSyntax& Parser::parseGenvarDeclaration(AttrList attributes) {
    Token keyword;
    Token semi;
    span<TokenOrSyntax> identifiers;

    parseList<isIdentifierOrComma, isSemicolon>(
        TokenKind::GenVarKeyword, TokenKind::Semicolon, TokenKind::Comma, keyword, identifiers,
        semi, RequireItems::True, diag::ExpectedIdentifier,
        [this] { return &factory.identifierName(consume()); });

    return factory.genvarDeclaration(attributes, keyword, identifiers, semi);
}

LoopGenerateSyntax& Parser::parseLoopGenerateConstruct(AttrList attributes) {
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

IfGenerateSyntax& Parser::parseIfGenerateConstruct(AttrList attributes) {
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

CaseGenerateSyntax& Parser::parseCaseGenerateConstruct(AttrList attributes) {
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

ClassDeclarationSyntax& Parser::parseClassDeclaration(AttrList attributes,
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

ContinuousAssignSyntax& Parser::parseContinuousAssign(AttrList attributes) {
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

DefParamSyntax& Parser::parseDefParam(AttrList attributes) {
    auto defparam = consume();
    SmallVectorSized<TokenOrSyntax, 8> buffer;

    Token semi;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedVariableAssignment, [this] { return &parseDefParamAssignment(); });

    return factory.defParam(attributes, defparam, buffer.copy(alloc), semi);
}

CoverageOptionSyntax* Parser::parseCoverageOption(AttrList attributes) {
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
        auto& type = parseDataType(TypeOptions::AllowImplicit);
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

CoverpointSyntax* Parser::parseCoverpoint(AttrList attributes, DataTypeSyntax* type,
                                          NamedLabelSyntax* label) {
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
        buffer.append(&parseOpenRangeElement());
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

CovergroupDeclarationSyntax& Parser::parseCovergroupDeclaration(AttrList attributes) {

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

MemberSyntax& Parser::parseConstraint(AttrList attributes, span<Token> qualifiers) {
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

span<PackageImportDeclarationSyntax*> Parser::parsePackageImports() {
    SmallVectorSized<PackageImportDeclarationSyntax*, 4> buffer;
    while (peek(TokenKind::ImportKeyword))
        buffer.append(&parseImportDeclaration({}));
    return buffer.copy(alloc);
}

PackageImportDeclarationSyntax& Parser::parseImportDeclaration(AttrList attributes) {
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

DPIImportExportSyntax& Parser::parseDPIImportExport(AttrList attributes) {
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
                        type = &parseDataType(TypeOptions::AllowImplicit);
                        break;
                    }
                    type = &factory.keywordType(SyntaxKind::PropertyType, consume());
                    break;
                case TokenKind::SequenceKeyword:
                    if (declarationKind == TokenKind::LetKeyword) {
                        type = &parseDataType(TypeOptions::AllowImplicit);
                        break;
                    }
                    type = &factory.keywordType(SyntaxKind::SequenceType, consume());
                    break;
                case TokenKind::UntypedKeyword:
                    type = &factory.keywordType(SyntaxKind::Untyped, consume());
                    break;
                default:
                    type = &parseDataType(TypeOptions::AllowImplicit);
                    break;
            }
            ASSERT(type);

            auto& declarator = parseDeclarator();
            return &factory.assertionItemPort(attributes, local, direction, *type, declarator);
        });

    return &factory.assertionItemPortList(openParen, buffer.copy(alloc), closeParen);
}

PropertyDeclarationSyntax& Parser::parsePropertyDeclaration(AttrList attributes) {

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

SequenceDeclarationSyntax& Parser::parseSequenceDeclaration(AttrList attributes) {

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

ClockingDeclarationSyntax& Parser::parseClockingDeclaration(AttrList attributes) {

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

            // TODO: this seems unfinished
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

HierarchyInstantiationSyntax& Parser::parseHierarchyInstantiation(AttrList attributes) {

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

} // namespace slang