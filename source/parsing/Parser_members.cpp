//------------------------------------------------------------------------------
// Parser_members.cpp
// Member-related parsing methods
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

namespace slang {

CompilationUnitSyntax& Parser::parseCompilationUnit() {
    try {
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::EndOfFile, eofToken, SyntaxKind::CompilationUnit,
            [this](SyntaxKind parentKind, bool& anyLocalModules) {
                return parseMember(parentKind, anyLocalModules);
            });
        return factory.compilationUnit(members, eofToken);
    }
    catch (const RecursionException&) {
        return factory.compilationUnit(nullptr, eofToken);
    }
}

ModuleDeclarationSyntax& Parser::parseModule() {
    bool anyLocalModules = false;
    return parseModule(parseAttributes(), SyntaxKind::CompilationUnit, anyLocalModules);
}

ModuleDeclarationSyntax& Parser::parseModule(AttrList attributes, SyntaxKind parentKind,
                                             bool& anyLocalModules) {
    // Tell the preprocessor that we're inside a design element for the duration of this function.
    auto& pp = getPP();
    pp.pushDesignElementStack();

    auto& header = parseModuleHeader();
    auto endKind = getModuleEndKind(header.moduleKeyword.kind);

    // If the parent isn't a compilation unit, that means we're a nested definition.
    // Record our name in the decl stack so that child instantiations know they're
    // referencing a local module and not a global one.
    if (parentKind != SyntaxKind::CompilationUnit) {
        auto name = header.name.valueText();
        if (!name.empty()) {
            if (!anyLocalModules) {
                moduleDeclStack.emplace();
                anyLocalModules = true;
            }
            moduleDeclStack.back().emplace(name);
        }
    }

    SyntaxKind declKind = getModuleDeclarationKind(header.moduleKeyword.kind);
    Metadata::Node node{ pp.getDefaultNetType(), pp.getUnconnectedDrive(), pp.getTimeScale() };

    Token endmodule;
    auto members = parseMemberList<MemberSyntax>(
        endKind, endmodule, declKind, [this](SyntaxKind parentKind, bool& anyLocalModules) {
            return parseMember(parentKind, anyLocalModules);
        });

    pp.popDesignElementStack();

    auto endName = parseNamedBlockClause();
    checkBlockNames(header.name, endName);

    auto& result =
        factory.moduleDeclaration(declKind, attributes, header, members, endmodule, endName);

    meta.nodeMap[&result] = node;
    return result;
}

ClassDeclarationSyntax& Parser::parseClass() {
    auto attributes = parseAttributes();

    Token virtualOrInterface;
    if (peek(TokenKind::VirtualKeyword) || peek(TokenKind::InterfaceKeyword))
        virtualOrInterface = consume();

    return parseClassDeclaration(attributes, virtualOrInterface);
}

MemberSyntax* Parser::parseMember(SyntaxKind parentKind, bool& anyLocalModules) {
    auto attributes = parseAttributes();

    if (isHierarchyInstantiation())
        return &parseHierarchyInstantiation(attributes);
    if (isPortDeclaration())
        return &parsePortDeclaration(attributes);
    if (isNetDeclaration())
        return &parseNetDeclaration(attributes);
    if (isVariableDeclaration())
        return &parseVariableDeclaration(attributes);

    Token token = peek();
    switch (token.kind) {
        case TokenKind::GenerateKeyword: {
            errorIfAttributes(attributes);
            auto keyword = consume();

            Token endgenerate;
            auto members = parseMemberList<MemberSyntax>(
                TokenKind::EndGenerateKeyword, endgenerate, SyntaxKind::GenerateRegion,
                [this](SyntaxKind parentKind, bool& anyLocalModules) {
                    return parseMember(parentKind, anyLocalModules);
                });
            return &factory.generateRegion(attributes, keyword, members, endgenerate);
        }
        case TokenKind::BeginKeyword:
            errorIfAttributes(attributes);

            // It's definitely not legal to have a generate block here on its own
            // (without an if or for loop) but some simulators seems to accept it
            // and I've found code in the wild that depends on it. We'll parse it
            // here and then issue a diagnostic about how it's not kosher.
            addDiag(diag::NonStandardGenBlock, token.location());
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
            return &parseModule(attributes, parentKind, anyLocalModules);
        case TokenKind::InterfaceKeyword:
            // an interface class is different from an interface
            if (peek(1).kind == TokenKind::ClassKeyword)
                return &parseClassDeclaration(attributes, consume());
            else
                return &parseModule(attributes, parentKind, anyLocalModules);
        case TokenKind::ModPortKeyword:
            return &parseModportDeclaration(attributes);
        case TokenKind::BindKeyword:
            return &parseBindDirective(attributes);
        case TokenKind::SpecParamKeyword:
        case TokenKind::AliasKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::SpecifyKeyword:
            // TODO: parse these
            break;
        case TokenKind::Identifier:
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

            // If there's a hash symbol here, it's probably a malformed instantiation.
            // Call into that handler to get a better error message than just skipping
            // the identifier token.
            if (peek(1).kind == TokenKind::Hash || peek(1).kind == TokenKind::OpenParenthesis)
                return &parseHierarchyInstantiation(attributes);

            // Otherwise, assume it's an attempt at a variable declaration.
            return &parseVariableDeclaration(attributes);
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
                                             TokenKind::EndTaskKeyword, parentKind);
        case TokenKind::FunctionKeyword:
            return &parseFunctionDeclaration(attributes, SyntaxKind::FunctionDeclaration,
                                             TokenKind::EndFunctionKeyword, parentKind);
        case TokenKind::CoverGroupKeyword:
            return &parseCovergroupDeclaration(attributes);
        case TokenKind::ClassKeyword:
            return &parseClassDeclaration(attributes, Token());
        case TokenKind::VirtualKeyword:
            if (peek(1).kind == TokenKind::ClassKeyword)
                return &parseClassDeclaration(attributes, consume());
            break;
        case TokenKind::DefParamKeyword:
            return &parseDefParam(attributes);
        case TokenKind::ImportKeyword:
            if (peek(1).kind == TokenKind::StringLiteral) {
                return &parseDPIImport(attributes);
            }
            return &parseImportDeclaration(attributes);
        case TokenKind::ExportKeyword:
            return &parseDPIExport(attributes);
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
        case TokenKind::SystemIdentifier: {
            auto result = parseElabSystemTask(attributes);
            if (result)
                return result;
            break;
        }
        default:
            break;
    }

    if (isGateType(token.kind))
        return &parseGateInstantiation(attributes);

    // If this is a class qualifier, maybe they accidentally put them
    // on an out-of-block method definition.
    if (isMethodQualifier(token.kind)) {
        Token t;
        uint32_t index = 0;
        do {
            t = peek(++index);
        } while (isMethodQualifier(t.kind));

        if (t.kind == TokenKind::FunctionKeyword || t.kind == TokenKind::TaskKeyword) {
            // Skip all the qualifiers.
            addDiag(diag::QualifiersOnOutOfBlock, token.location()) << token.range();
            for (uint32_t i = 0; i < index; i++)
                skipToken(std::nullopt);

            auto kind = t.kind == TokenKind::FunctionKeyword ? SyntaxKind::FunctionDeclaration
                                                             : SyntaxKind::TaskDeclaration;
            return &parseFunctionDeclaration(attributes, kind, getSkipToKind(t.kind), parentKind);
        }
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(
            attributes, nullptr,
            Token::createMissing(alloc, TokenKind::Semicolon, token.location()));
    }

    // Otherwise, we got nothing and should just return null so that our
    // caller will skip and try again.
    return nullptr;
}

MemberSyntax* Parser::parseSingleMember(SyntaxKind parentKind) {
    bool anyLocalModules = false;
    auto result = parseMember(parentKind, anyLocalModules);
    if (anyLocalModules)
        moduleDeclStack.pop();

    if (result)
        checkMemberAllowed(*result, parentKind);

    return result;
}

template<typename TMember, typename TParseFunc>
span<TMember*> Parser::parseMemberList(TokenKind endKind, Token& endToken, SyntaxKind parentKind,
                                       TParseFunc&& parseFunc) {
    SmallVectorSized<TMember*, 16> members;
    bool errored = false;
    bool anyLocalModules = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || kind == endKind)
            break;

        auto member = parseFunc(parentKind, anyLocalModules);
        if (member) {
            checkMemberAllowed(*member, parentKind);
            members.append(member);
            errored = false;
        }
        else {
            skipToken(errored ? std::nullopt : std::make_optional(diag::ExpectedMember));
            errored = true;
        }
    }

    if (anyLocalModules)
        moduleDeclStack.pop();

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
            auto& proto =
                parseFunctionPrototype(SyntaxKind::Unknown, FunctionOptions::AllowEmptyArgNames |
                                                                FunctionOptions::AllowTasks);
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
                expr = &parseExpression();

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

FunctionPortSyntax& Parser::parseFunctionPort(bool allowEmptyName) {
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

    DeclaratorSyntax* decl;
    if (!allowEmptyName || peek(TokenKind::Identifier) || peek(TokenKind::Equals))
        decl = &parseDeclarator();
    else
        decl = &factory.declarator(placeholderToken(), nullptr, nullptr);

    return factory.functionPort(attributes, constKeyword, direction, varKeyword, dataType, *decl);
}

static bool checkSubroutineName(const NameSyntax& name) {
    auto checkKind = [](auto& node) {
        return node.kind == SyntaxKind::IdentifierName || node.kind == SyntaxKind::ConstructorName;
    };

    if (name.kind == SyntaxKind::ScopedName) {
        auto& scoped = name.as<ScopedNameSyntax>();
        if (scoped.separator.kind == TokenKind::Dot)
            return false;

        return checkKind(*scoped.left) && checkKind(*scoped.right);
    }

    return checkKind(name);
}

FunctionPrototypeSyntax& Parser::parseFunctionPrototype(SyntaxKind parentKind,
                                                        bitmask<FunctionOptions> options,
                                                        bool* isConstructor) {
    Token keyword;
    if (options.has(FunctionOptions::AllowTasks) && peek(TokenKind::TaskKeyword))
        keyword = consume();
    else
        keyword = expect(TokenKind::FunctionKeyword);

    auto lifetime = parseLifetime();

    // Return type is optional for function declarations, and should not be given
    // for tasks and constructors (we'll check that below).
    DataTypeSyntax* returnType = nullptr;
    uint32_t index = 0;
    if (!scanQualifiedName(index, /* allowNew */ true))
        returnType = &parseDataType(TypeOptions::AllowImplicit | TypeOptions::AllowVoid);
    else {
        auto next = peek(index);
        if (next.kind != TokenKind::Semicolon && next.kind != TokenKind::OpenParenthesis)
            returnType = &parseDataType(TypeOptions::AllowImplicit | TypeOptions::AllowVoid);
        else
            returnType = &factory.implicitType(Token(), nullptr);
    }

    auto& name = parseName();
    if (!checkSubroutineName(name))
        addDiag(diag::ExpectedSubroutineName, keyword.location()) << name.sourceRange();

    bool constructor = getLastConsumed().kind == TokenKind::NewKeyword;
    if (isConstructor)
        *isConstructor = constructor;

    if (keyword.kind == TokenKind::TaskKeyword) {
        if (returnType->kind != SyntaxKind::ImplicitType)
            addDiag(diag::TaskReturnType, keyword.location()) << returnType->sourceRange();
        else if (constructor)
            addDiag(diag::TaskConstructor, keyword.location()) << name.sourceRange();
    }
    else if (constructor && returnType->kind != SyntaxKind::ImplicitType) {
        addDiag(diag::ConstructorReturnType, name.getFirstToken().location())
            << returnType->sourceRange();
    }
    else if (constructor && name.kind != SyntaxKind::ScopedName &&
             parentKind != SyntaxKind::ClassDeclaration) {
        addDiag(diag::ConstructorOutsideClass, keyword.location()) << name.sourceRange();
    }
    else if (!constructor && !options.has(FunctionOptions::AllowImplicitReturn) &&
             returnType->kind == SyntaxKind::ImplicitType) {
        addDiag(diag::ImplicitNotAllowed, name.getFirstToken().location());
    }

    const bool allowEmptyNames = options.has(FunctionOptions::AllowEmptyArgNames);
    FunctionPortListSyntax* portList = nullptr;
    if (peek(TokenKind::OpenParenthesis)) {
        auto openParen = consume();
        Token closeParen;
        SmallVectorSized<TokenOrSyntax, 8> buffer;
        parseList<isPossibleFunctionPort, isEndOfParenList>(
            buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
            diag::ExpectedFunctionPort,
            [this, allowEmptyNames] { return &parseFunctionPort(allowEmptyNames); });

        portList = &factory.functionPortList(openParen, buffer.copy(alloc), closeParen);
    }

    return factory.functionPrototype(keyword, lifetime, *returnType, name, portList);
}

FunctionDeclarationSyntax& Parser::parseFunctionDeclaration(AttrList attributes,
                                                            SyntaxKind functionKind,
                                                            TokenKind endKind,
                                                            SyntaxKind parentKind) {
    Token end;
    bool isConstructor;
    auto& prototype = parseFunctionPrototype(
        parentKind, FunctionOptions::AllowImplicitReturn | FunctionOptions::AllowTasks,
        &isConstructor);

    auto semi = expect(TokenKind::Semicolon);
    auto items = parseBlockItems(endKind, end, isConstructor);
    auto endBlockName = parseNamedBlockClause();

    Token nameToken = prototype.name->getLastToken();
    if (nameToken.kind == TokenKind::Identifier || nameToken.kind == TokenKind::NewKeyword)
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
            auto member = parseSingleMember(SyntaxKind::GenerateBlock);
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
    auto members =
        parseMemberList<MemberSyntax>(TokenKind::EndKeyword, end, SyntaxKind::GenerateBlock,
                                      [this](SyntaxKind parentKind, bool& anyLocalModules) {
                                          return parseMember(parentKind, anyLocalModules);
                                      });

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
    bool isIfaceClass = virtualOrInterface.kind == TokenKind::InterfaceKeyword;
    if (isIfaceClass)
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
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndClassKeyword, endClass, SyntaxKind::ClassDeclaration,
        [this, isIfaceClass](SyntaxKind, bool&) { return parseClassMember(isIfaceClass); });

    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.classDeclaration(attributes, virtualOrInterface, classKeyword, lifetime, name,
                                    parameterList, extendsClause, implementsClause, semi, members,
                                    endClass, endBlockName);
}

void Parser::checkClassQualifiers(span<const Token> qualifiers, bool isConstraint) {
    SmallMap<TokenKind, Token, 4> qualifierSet;
    Token lastRand;
    Token lastVisibility;
    Token lastStaticOrVirtual;
    Token lastPure;
    bool isVirtual = false;
    bool errorDup = false;
    bool errorRand = false;
    bool errorVisibility = false;
    bool errorStaticVirtual = false;
    bool errorFirst = false;
    bool errorPure = false;
    size_t count = 0;

    auto checkConflict = [this](Token curr, bool isKind, Token& lastSeen, bool& alreadyErrored) {
        if (isKind) {
            if (lastSeen) {
                if (!alreadyErrored) {
                    auto& diag = addDiag(diag::QualifierConflict, curr.location());
                    diag << curr.rawText() << curr.range();
                    diag << lastSeen.rawText() << lastSeen.range();
                    alreadyErrored = true;
                }
                return;
            }
            lastSeen = curr;
        }
    };

    for (auto t : qualifiers) {
        count++;
        if (t.kind == TokenKind::VirtualKeyword)
            isVirtual = true;

        // Don't allow duplicates of any qualifier.
        if (auto [it, inserted] = qualifierSet.emplace(t.kind, t); !inserted) {
            if (!errorDup) {
                auto& diag = addDiag(diag::DuplicateQualifier, t.location());
                diag << t.rawText() << t.range() << it->second.range();
                errorDup = true;
            }
            continue;
        }

        // Some qualifiers are required to come first in the list.
        if (count > 1 && (t.kind == TokenKind::PureKeyword || t.kind == TokenKind::ExternKeyword)) {
            if (!errorFirst) {
                auto& diag = addDiag(diag::QualifierNotFirst, t.location());
                diag << t.rawText() << t.range();
                errorFirst = true;
            }
            continue;
        }

        // Pure keyword must be followed by virtual unless this is a constraint.
        if (t.kind == TokenKind::PureKeyword)
            lastPure = t;
        else if (lastPure) {
            if (t.kind != TokenKind::VirtualKeyword && !isConstraint) {
                if (!errorPure) {
                    auto& diag = addDiag(diag::PureRequiresVirtual, t.location());
                    diag << lastPure.range() << t.range();
                    errorPure = true;
                }
                continue;
            }
            lastPure = Token();
        }

        // rand, randc, and const are mutually exclusive.
        checkConflict(t,
                      t.kind == TokenKind::RandKeyword || t.kind == TokenKind::RandCKeyword ||
                          t.kind == TokenKind::ConstKeyword,
                      lastRand, errorRand);

        // local and protected are mutually exclusive.
        checkConflict(t, t.kind == TokenKind::LocalKeyword || t.kind == TokenKind::ProtectedKeyword,
                      lastVisibility, errorVisibility);

        // static and virtual are mutually exclusive.
        checkConflict(t, t.kind == TokenKind::StaticKeyword || t.kind == TokenKind::VirtualKeyword,
                      lastStaticOrVirtual, errorStaticVirtual);
    }

    if (lastPure && !errorPure && !isVirtual && !isConstraint)
        addDiag(diag::PureRequiresVirtual, lastPure.location()) << lastPure.range();
}

MemberSyntax* Parser::parseClassMember(bool isIfaceClass) {
    auto errorIfIface = [&](const SyntaxNode& syntax) {
        if (isIfaceClass) {
            auto range = syntax.sourceRange();
            addDiag(diag::NotAllowedInIfaceClass, range.start()) << range;
        }
    };

    auto attributes = parseAttributes();

    // virtual keyword can either be a class decl, virtual interface, or a method qualifier;
    // early out here if it's a class or interface
    if (peek(TokenKind::VirtualKeyword)) {
        switch (peek(1).kind) {
            case TokenKind::ClassKeyword: {
                auto& result = parseClassDeclaration(attributes, consume());
                errorIfIface(result);
                return &result;
            }
            case TokenKind::InterfaceKeyword: {
                auto& result = factory.classPropertyDeclaration(attributes, nullptr,
                                                                parseVariableDeclaration({}));
                errorIfIface(result);
                return &result;
            }
            default:
                break;
        }
    }

    bool isPureOrExtern = false;
    SmallVectorSized<Token, 4> qualifierBuffer;
    while (isMemberQualifier(peek().kind)) {
        Token t = consume();
        qualifierBuffer.append(t);
        if (t.kind == TokenKind::PureKeyword || t.kind == TokenKind::ExternKeyword)
            isPureOrExtern = true;
    }

    auto qualifiers = qualifierBuffer.copy(alloc);
    checkClassQualifiers(qualifiers, peek(TokenKind::ConstraintKeyword));

    if (isVariableDeclaration()) {
        // Check that all qualifiers are allowed specifically for properties.
        Token lastLifetime;
        for (auto qual : qualifiers) {
            if (!isPropertyQualifier(qual.kind)) {
                auto& diag = addDiag(diag::InvalidPropertyQualifier, qual.location());
                diag << qual.range() << qual.rawText();
                break;
            }

            if (isLifetimeModifier(qual.kind))
                lastLifetime = qual;
        }

        auto& decl = parseVariableDeclaration({});
        if (decl.kind == SyntaxKind::DataDeclaration) {
            // Make sure qualifiers weren't duplicated in the data declaration's modifiers.
            // Note that we don't have to check for `const` here because parseVariableDeclaration
            // will error if the const keyword isn't first, but if it was first we would have
            // already consumed it ourselves as a qualifier.
            for (auto mod : decl.as<DataDeclarationSyntax>().modifiers) {
                if (isLifetimeModifier(mod.kind) && lastLifetime) {
                    if (mod.kind == lastLifetime.kind) {
                        auto& diag = addDiag(diag::DuplicateQualifier, mod.location());
                        diag << mod.rawText() << mod.range() << lastLifetime.range();
                    }
                    else {
                        auto& diag = addDiag(diag::QualifierConflict, mod.location());
                        diag << mod.rawText() << mod.range();
                        diag << lastLifetime.rawText() << lastLifetime.range();
                    }
                    break;
                }
            }

            errorIfIface(decl);
        }
        else if (decl.kind == SyntaxKind::PackageImportDeclaration ||
                 decl.kind == SyntaxKind::NetTypeDeclaration ||
                 decl.kind == SyntaxKind::LetDeclaration) {
            // Nettypes and package imports are disallowed in classes.
            SourceRange range = decl.sourceRange();
            addDiag(diag::NotAllowedInClass, range.start()) << range;
        }
        else {
            // Otherwise, check for invalid qualifiers.
            for (auto qual : qualifiers) {
                if (isIfaceClass) {
                    addDiag(diag::InvalidQualifierForIfaceMember, qual.location()) << qual.range();
                    break;
                }

                switch (qual.kind) {
                    case TokenKind::RandKeyword:
                    case TokenKind::RandCKeyword:
                    case TokenKind::ConstKeyword:
                    case TokenKind::StaticKeyword:
                        addDiag(diag::InvalidQualifierForMember, qual.location()) << qual.range();
                        break;
                    case TokenKind::LocalKeyword:
                    case TokenKind::ProtectedKeyword:
                        if (decl.kind == SyntaxKind::ParameterDeclarationStatement)
                            addDiag(diag::InvalidQualifierForMember, qual.location())
                                << qual.range();
                        break;
                    default:
                        break;
                }
            }
        }

        return &factory.classPropertyDeclaration(attributes, qualifiers, decl);
    }

    auto kind = peek().kind;
    if (kind == TokenKind::TaskKeyword || kind == TokenKind::FunctionKeyword) {
        // Check that qualifiers are allowed specifically for methods.
        bool isPure = false;
        for (auto qual : qualifiers) {
            if (qual.kind == TokenKind::PureKeyword)
                isPure = true;

            if (!isMethodQualifier(qual.kind)) {
                auto& diag = addDiag(diag::InvalidMethodQualifier, qual.location());
                diag << qual.range() << qual.rawText();
                isPure = true;
                break;
            }

            if (isIfaceClass && qual.kind != TokenKind::PureKeyword &&
                qual.kind != TokenKind::VirtualKeyword) {
                addDiag(diag::InvalidQualifierForIfaceMember, qual.location()) << qual.range();
                isPure = true;
                break;
            }
        }

        if (isIfaceClass && !isPure)
            addDiag(diag::IfaceMethodPure, peek().location());

        auto checkProto = [this, &qualifiers](auto& proto) {
            if (proto.lifetime.kind == TokenKind::StaticKeyword) {
                auto& diag = addDiag(diag::MethodStaticLifetime, proto.lifetime.location());
                diag << proto.lifetime.range();
            }

            // Additional checking for constructors.
            auto lastNamePart = proto.name->getLastToken();
            if (lastNamePart.kind == TokenKind::NewKeyword) {
                for (auto qual : qualifiers) {
                    if (qual.kind == TokenKind::VirtualKeyword ||
                        qual.kind == TokenKind::StaticKeyword) {
                        addDiag(diag::InvalidQualifierForConstructor, qual.location())
                            << qual.range();
                        break;
                    }
                }
            }
        };

        // Pure or extern functions don't have bodies.
        if (isPureOrExtern) {
            auto& proto =
                parseFunctionPrototype(SyntaxKind::ClassDeclaration, FunctionOptions::AllowTasks);
            checkProto(proto);

            if (proto.name->kind == SyntaxKind::ScopedName)
                addDiag(diag::MethodPrototypeScoped, proto.name->getFirstToken().location());

            return &factory.classMethodPrototype(attributes, qualifiers, proto,
                                                 expect(TokenKind::Semicolon));
        }
        else {
            auto declKind = kind == TokenKind::TaskKeyword ? SyntaxKind::TaskDeclaration
                                                           : SyntaxKind::FunctionDeclaration;
            auto endKind = kind == TokenKind::TaskKeyword ? TokenKind::EndTaskKeyword
                                                          : TokenKind::EndFunctionKeyword;
            auto& funcDecl =
                parseFunctionDeclaration({}, declKind, endKind, SyntaxKind::ClassDeclaration);
            checkProto(*funcDecl.prototype);

            // If this is a scoped name, it should be an out-of-block definition for
            // a method declared in a nested class. Qualifiers are not allowed here.
            if (funcDecl.prototype->name->kind == SyntaxKind::ScopedName && !qualifiers.empty()) {
                addDiag(diag::QualifiersOnOutOfBlock, qualifiers[0].location())
                    << qualifiers[0].range();
            }

            return &factory.classMethodDeclaration(attributes, qualifiers, funcDecl);
        }
    }

    if (kind == TokenKind::ConstraintKeyword) {
        auto& result = parseConstraint(attributes, qualifiers);
        errorIfIface(result);
        return &result;
    }

    // Qualifiers aren't allowed past this point, so return an empty member to hold them.
    if (!qualifiers.empty()) {
        addDiag(diag::UnexpectedQualifiers, qualifiers[0].location());
        return &factory.emptyMember(
            attributes, qualifiers,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    switch (kind) {
        case TokenKind::ClassKeyword: {
            auto& result = parseClassDeclaration(attributes, Token());
            errorIfIface(result);
            return &result;
        }
        case TokenKind::CoverGroupKeyword: {
            auto& result = parseCovergroupDeclaration(attributes);
            errorIfIface(result);
            return &result;
        }
        case TokenKind::Semicolon:
            errorIfAttributes(attributes);
            return &factory.emptyMember(attributes, qualifiers, consume());
        case TokenKind::InterfaceKeyword:
            if (peek(1).kind == TokenKind::ClassKeyword) {
                addDiag(diag::NestedIface, peek().location());
                return &parseClassDeclaration(attributes, consume());
            }
            break;
        default:
            break;
    }

    // If we got attributes but don't know what comes next, we have some kind of nonsense.
    if (!attributes.empty()) {
        return &factory.emptyMember(
            attributes, qualifiers,
            Token::createMissing(alloc, TokenKind::Semicolon, peek().location()));
    }

    // Otherwise, we got nothing and should just return null so that our caller will skip and try
    // again.
    return nullptr;
}

ContinuousAssignSyntax& Parser::parseContinuousAssign(AttrList attributes) {
    auto assign = consume();
    auto strength = parseDriveStrength();
    auto delay = parseDelay3();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedContinuousAssignment, [this] {
            auto& expr = parseExpression();
            if (expr.kind != SyntaxKind::AssignmentExpression) {
                addDiag(diag::ExpectedContinuousAssignment, expr.getFirstToken().location())
                    << expr.sourceRange();
            }
            return &expr;
        });

    return factory.continuousAssign(attributes, assign, strength, delay, buffer.copy(alloc), semi);
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

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> buffer;
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
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::CloseBrace, closeBrace, SyntaxKind::Coverpoint,
            [this](SyntaxKind, bool&) { return parseCoverpointMember(); });

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

    CoverageIffClauseSyntax* iffClause = nullptr;
    if (peek(TokenKind::IffKeyword)) {
        auto iff = consume();
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpression();
        iffClause =
            &factory.coverageIffClause(iff, openParen, expr, expect(TokenKind::CloseParenthesis));
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
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndGroupKeyword, endGroup, SyntaxKind::CovergroupDeclaration,
        [this](SyntaxKind, bool&) { return parseCoverageMember(); });

    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.covergroupDeclaration(attributes, keyword, name, portList, event, semi, members,
                                         endGroup, endBlockName);
}

MemberSyntax& Parser::parseConstraint(AttrList attributes, span<Token> qualifiers) {
    for (auto qual : qualifiers) {
        if (!isConstraintQualifier(qual.kind)) {
            auto& diag = addDiag(diag::InvalidConstraintQualifier, qual.location());
            diag << qual.range() << qual.rawText();
            break;
        }
    }

    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);

    if (peek(TokenKind::OpenBrace)) {
        return factory.constraintDeclaration(attributes, qualifiers, keyword, name,
                                             parseConstraintBlock(/* isTopLevel */ true));
    }

    return factory.constraintPrototype(attributes, qualifiers, keyword, name, consume());
}

ConstraintBlockSyntax& Parser::parseConstraintBlock(bool isTopLevel) {
    Token closeBrace;
    auto openBrace = expect(TokenKind::OpenBrace);
    auto members = parseMemberList<ConstraintItemSyntax>(
        TokenKind::CloseBrace, closeBrace, SyntaxKind::ConstraintBlock,
        [this, isTopLevel](SyntaxKind, bool&) { return parseConstraintItem(false, isTopLevel); });

    return factory.constraintBlock(openBrace, members, closeBrace);
}

ExpressionSyntax& Parser::parseExpressionOrDist() {
    auto& expr = parseExpression();
    if (!peek(TokenKind::DistKeyword))
        return expr;

    auto& dist = parseDistConstraintList();
    return factory.expressionOrDist(expr, dist);
}

ConstraintItemSyntax* Parser::parseConstraintItem(bool allowBlock, bool isTopLevel) {
    switch (peek().kind) {
        case TokenKind::SolveKeyword: {
            auto solve = consume();
            if (!isTopLevel)
                addDiag(diag::SolveBeforeDisallowed, solve.location()) << solve.range();

            Token before;
            SmallVectorSized<TokenOrSyntax, 4> beforeBuffer;
            parseList<isPossibleExpressionOrComma, isBeforeOrSemicolon>(
                beforeBuffer, TokenKind::BeforeKeyword, TokenKind::Comma, before,
                RequireItems::True, diag::ExpectedExpression,
                [this] { return &parsePrimaryExpression(/* disallowVector */ false); });

            Token semi;
            SmallVectorSized<TokenOrSyntax, 4> afterBuffer;
            parseList<isPossibleExpressionOrComma, isSemicolon>(
                afterBuffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
                diag::ExpectedExpression,
                [this] { return &parsePrimaryExpression(/* disallowVector */ false); });

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
            return &factory.loopConstraint(keyword, vars, *parseConstraintItem(true, false));
        }
        case TokenKind::IfKeyword: {
            auto ifKeyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& condition = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& constraints = *parseConstraintItem(true, false);

            ElseConstraintClauseSyntax* elseClause = nullptr;
            if (peek(TokenKind::ElseKeyword)) {
                auto elseKeyword = consume();
                elseClause =
                    &factory.elseConstraintClause(elseKeyword, *parseConstraintItem(true, false));
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
                                                            TokenKind::CloseBrace)) {
                    return &parseConstraintBlock(false);
                }
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
        return &factory.implicationConstraint(*expr, arrow, *parseConstraintItem(true, false));
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

Token Parser::parseDPISpecString() {
    Token token = expect(TokenKind::StringLiteral);
    if (!token.isMissing() && token.valueText() != "DPI-C" && token.valueText() != "DPI")
        addDiag(diag::ExpectedDPISpecString, token.location());
    return token;
}

DPIImportSyntax& Parser::parseDPIImport(AttrList attributes) {
    Token keyword = consume();
    Token specString = parseDPISpecString();

    Token property;
    if (peek(TokenKind::ContextKeyword) || peek(TokenKind::PureKeyword))
        property = consume();

    Token c_identifier, equals;
    if (peek(TokenKind::Identifier)) {
        c_identifier = consume();
        equals = expect(TokenKind::Equals);
    }

    bitmask<FunctionOptions> options = FunctionOptions::AllowEmptyArgNames;
    if (property.kind != TokenKind::PureKeyword)
        options |= FunctionOptions::AllowTasks;

    auto& method = parseFunctionPrototype(SyntaxKind::Unknown, options);
    Token semi = expect(TokenKind::Semicolon);
    return factory.dPIImport(attributes, keyword, specString, property, c_identifier, equals,
                             method, semi);
}

DPIExportSyntax& Parser::parseDPIExport(AttrList attributes) {
    Token keyword = consume();
    Token specString = parseDPISpecString();

    Token c_identifier, equals;
    if (peek(TokenKind::Identifier)) {
        c_identifier = consume();
        equals = expect(TokenKind::Equals);
    }

    Token functionOrTask;
    if (peek(TokenKind::TaskKeyword))
        functionOrTask = consume();
    else
        functionOrTask = expect(TokenKind::FunctionKeyword);

    Token name = expect(TokenKind::Identifier);
    Token semi = expect(TokenKind::Semicolon);
    return factory.dPIExport(attributes, keyword, specString, c_identifier, equals, functionOrTask,
                             name, semi);
}

ElabSystemTaskSyntax* Parser::parseElabSystemTask(AttrList attributes) {
    auto name = peek().valueText();
    if (name != "$fatal"sv && name != "$error"sv && name != "$warning"sv && name != "$info"sv)
        return nullptr;

    auto nameToken = consume();
    ArgumentListSyntax* argList = nullptr;
    if (peek(TokenKind::OpenParenthesis))
        argList = &parseArgumentList();

    return &factory.elabSystemTask(attributes, nameToken, argList, expect(TokenKind::Semicolon));
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
    Token edge;
    switch (peek().kind) {
        case TokenKind::EdgeKeyword:
        case TokenKind::PosEdgeKeyword:
        case TokenKind::NegEdgeKeyword:
            edge = consume();
            break;
        default:
            break;
    }

    DelaySyntax* delay = nullptr;
    if (peek(TokenKind::Hash)) {
        Token hash = consume();
        delay = &factory.delay(SyntaxKind::DelayControl, hash,
                               parsePrimaryExpression(/* disallowVector */ true));
    }

    if (!edge && !delay)
        return nullptr;

    return &factory.clockingSkew(edge, delay);
}

MemberSyntax* Parser::parseClockingItem() {
    Token def;
    switch (peek().kind) {
        case TokenKind::DefaultKeyword:
            def = consume();
            break;
        case TokenKind::InputKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::InOutKeyword:
            break;
        default:
            return parseSingleMember(SyntaxKind::ClockingItem);
    }

    Token input, output;
    ClockingSkewSyntax* inputSkew = nullptr;
    ClockingSkewSyntax* outputSkew = nullptr;
    if (peek(TokenKind::InOutKeyword)) {
        input = consume();
        if (def)
            addDiag(diag::InOutDefaultSkew, input.location());
    }
    else {
        if (peek(TokenKind::InputKeyword)) {
            input = consume();
            inputSkew = parseClockingSkew();
            if (def && !inputSkew)
                addDiag(diag::ExpectedClockingSkew, input.location() + input.rawText().length());
        }

        if (peek(TokenKind::OutputKeyword)) {
            output = consume();
            outputSkew = parseClockingSkew();
            if (def && !outputSkew)
                addDiag(diag::ExpectedClockingSkew, output.location() + output.rawText().length());
        }

        if (def && !input && !output)
            addDiag(diag::ExpectedClockingSkew, def.location() + def.valueText().length());
    }

    auto& direction = factory.clockingDirection(input, inputSkew, output, outputSkew);
    if (def)
        return &factory.defaultSkewItem(nullptr, def, direction, expect(TokenKind::Semicolon));

    Token semi;
    SmallVectorSized<TokenOrSyntax, 4> decls;
    parseList<isIdentifierOrComma, isSemicolon>(decls, TokenKind::Semicolon, TokenKind::Comma, semi,
                                                RequireItems::True, diag::ExpectedIdentifier,
                                                [this] { return &parseAttributeSpec(); });

    return &factory.clockingItem(nullptr, direction, decls.copy(alloc), semi);
}

MemberSyntax& Parser::parseClockingDeclaration(AttrList attributes) {
    Token globalOrDefault;
    if (!peek(TokenKind::ClockingKeyword))
        globalOrDefault = consume();

    Token clocking = expect(TokenKind::ClockingKeyword);
    Token blockName = consumeIf(TokenKind::Identifier);

    // If this is a default reference there is no body to parse.
    if (globalOrDefault.kind == TokenKind::DefaultKeyword && blockName &&
        peek(TokenKind::Semicolon)) {
        return factory.defaultClockingReference(attributes, globalOrDefault, clocking, blockName,
                                                consume());
    }

    Token at = expect(TokenKind::At);

    EventExpressionSyntax* event;
    if (peek(TokenKind::OpenParenthesis))
        event = &parseEventExpression();
    else {
        auto& name = parseName();
        event = &factory.signalEventExpression({}, name, nullptr);
    }

    Token semi = expect(TokenKind::Semicolon);
    Token endClocking;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndClockingKeyword, endClocking, SyntaxKind::ClockingDeclaration,
        [this](SyntaxKind, bool&) { return parseClockingItem(); });

    if (globalOrDefault.kind == TokenKind::GlobalKeyword && !members.empty())
        addDiag(diag::GlobalClockingEmpty, members[0]->getFirstToken().location());

    NamedBlockClauseSyntax* endBlockName = parseNamedBlockClause();
    checkBlockNames(blockName, endBlockName);

    return factory.clockingDeclaration(attributes, globalOrDefault, clocking, blockName, at, *event,
                                       semi, members, endClocking, endBlockName);
}

HierarchyInstantiationSyntax& Parser::parseHierarchyInstantiation(AttrList attributes) {
    auto type = expect(TokenKind::Identifier);
    auto parameters = parseParameterValueAssignment();

    // If this is an instantiation of a global module/interface/program,
    // keep track of it in our instantiatedModules set.
    string_view name = type.valueText();
    if (!name.empty()) {
        bool found = false;
        for (auto& set : moduleDeclStack) {
            if (set.find(name) != set.end()) {
                found = true;
                break;
            }
        }
        if (!found)
            meta.globalInstances.emplace(name);
    }

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
        [this] { return &parsePortConnection(); }, AllowEmpty::True);

    return factory.hierarchicalInstance(name, dimensions, openParen, items, closeParen);
}

GateInstantiationSyntax& Parser::parseGateInstantiation(AttrList attributes) {
    auto type = consume();

    DriveStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis) && isDriveStrength(peek(1).kind))
        strength = parseDriveStrength(); // TODO: also pulldown strength

    auto delay = parseDelay3();

    Token semi;
    SmallVectorSized<TokenOrSyntax, 8> items;
    parseList<isPossibleGateInstance, isSemicolon>(
        items, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedGateInstance, [this] { return &parseGateInstance(); });

    return factory.gateInstantiation(attributes, type, strength, delay, items.copy(alloc), semi);
}

GateInstanceSyntax& Parser::parseGateInstance() {
    GateInstanceNameSyntax* decl = nullptr;
    if (peek(TokenKind::Identifier)) {
        auto name = expect(TokenKind::Identifier);
        auto dimensions = parseDimensionList();
        decl = &factory.gateInstanceName(name, dimensions);
    }

    Token openParen;
    Token closeParen;
    span<TokenOrSyntax> items;

    parseList<isPossibleExpressionOrComma, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, items,
        closeParen, RequireItems::True, diag::ExpectedPortConnection,
        [this] { return &parseExpression(); });

    return factory.gateInstance(decl, openParen, items, closeParen);
}

BindDirectiveSyntax& Parser::parseBindDirective(AttrList attr) {
    Token keyword = consume();
    auto& target = parseName();

    BindTargetListSyntax* targetInstances = nullptr;
    if (peek(TokenKind::Colon)) {
        auto colon = consume();

        SmallVectorSized<TokenOrSyntax, 4> names;
        while (true) {
            names.append(&parseName());
            if (!peek(TokenKind::Comma))
                break;

            names.append(consume());
        }

        targetInstances = &factory.bindTargetList(colon, names.copy(alloc));
    }

    auto& instantiation = parseHierarchyInstantiation({});
    auto& result = factory.bindDirective(attr, keyword, target, targetInstances, instantiation);

    meta.bindDirectives.append(&result);
    return result;
}

void Parser::checkMemberAllowed(const SyntaxNode& member, SyntaxKind parentKind) {
    // If this is an empty member with a missing semicolon, it was some kind
    // of error that has already been reported so don't pile on here.
    if (member.kind == SyntaxKind::EmptyMember) {
        if (member.as<EmptyMemberSyntax>().semi.isMissing())
            return;
    }

    auto error = [&](DiagCode code) {
        SourceRange range = member.sourceRange();
        addDiag(code, range.start()) << range;
    };

    switch (parentKind) {
        case SyntaxKind::CompilationUnit:
            if (!isAllowedInCompilationUnit(member.kind))
                error(diag::NotAllowedInCU);
            return;
        case SyntaxKind::GenerateBlock:
        case SyntaxKind::GenerateRegion:
            if (!isAllowedInGenerate(member.kind))
                error(diag::NotAllowedInGenerate);
            return;
        case SyntaxKind::ModuleDeclaration:
            if (!isAllowedInModule(member.kind))
                error(diag::NotAllowedInModule);
            return;
        case SyntaxKind::InterfaceDeclaration:
            if (!isAllowedInInterface(member.kind))
                error(diag::NotAllowedInInterface);
            return;
        case SyntaxKind::ProgramDeclaration:
            if (!isAllowedInProgram(member.kind))
                error(diag::NotAllowedInProgram);
            return;
        case SyntaxKind::PackageDeclaration:
            if (!isAllowedInPackage(member.kind))
                error(diag::NotAllowedInPackage);
            return;
        case SyntaxKind::ClockingItem:
            if (!isAllowedInClocking(member.kind))
                error(diag::NotAllowedInClocking);
            return;

        // Some kinds of parents already restrict the members they will parse
        // so there's no need to check them here.
        case SyntaxKind::ClassDeclaration:
        case SyntaxKind::Coverpoint:
        case SyntaxKind::CovergroupDeclaration:
        case SyntaxKind::ConstraintBlock:
        case SyntaxKind::ClockingDeclaration:
            return;
        default:
            THROW_UNREACHABLE;
    }
}

} // namespace slang
