//------------------------------------------------------------------------------
// Parser_members.cpp
// Member-related parsing methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/util/String.h"

namespace slang::parsing {

using namespace syntax;

CompilationUnitSyntax& Parser::parseCompilationUnit() {
    SLANG_TRY {
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::EndOfFile, meta.eofToken, SyntaxKind::CompilationUnit,
            [this](SyntaxKind parentKind, bool& anyLocalModules) {
                return parseMember(parentKind, anyLocalModules);
            });
        return factory.compilationUnit(members, meta.eofToken);
    }
    SLANG_CATCH(const RecursionException&) {
        return factory.compilationUnit(nullptr, meta.eofToken);
    }
}

LibraryMapSyntax& Parser::parseLibraryMap() {
    SLANG_TRY {
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::EndOfFile, meta.eofToken, SyntaxKind::LibraryMap,
            [this](SyntaxKind, bool&) { return parseLibraryMember(); });

        return factory.libraryMap(members, meta.eofToken);
    }
    SLANG_CATCH(const RecursionException&) {
        return factory.libraryMap(nullptr, meta.eofToken);
    }
}

SDFUnitSyntax& Parser::parseSDFUnit() {
    SLANG_TRY {
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::EndOfFile, meta.eofToken, SyntaxKind::SDFUnit,
            [this](SyntaxKind, bool&) { return parseSDFDelayFile(); }, /*memberLimit =*/1);

        return factory.sDFUnit(members, meta.eofToken);
    }
    SLANG_CATCH(const RecursionException&) {
        return factory.sDFUnit(nullptr, meta.eofToken);
    }
}

MemberSyntax& Parser::parseModule() {
    bool anyLocalModules = false;
    return parseModule(parseAttributes(), SyntaxKind::CompilationUnit, anyLocalModules);
}

MemberSyntax& Parser::parseModule(AttrList attributes, SyntaxKind parentKind,
                                  bool& anyLocalModules) {
    if (peek(TokenKind::ProgramKeyword) && peek(1).kind == TokenKind::Semicolon)
        return parseAnonymousProgram(attributes);

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
                moduleDeclStack.emplace_back();
                anyLocalModules = true;
            }
            moduleDeclStack.back().emplace(name);
        }
    }

    SyntaxKind declKind = getModuleDeclarationKind(header.moduleKeyword.kind);
    ParserMetadata::Node node{pp.getDefaultNetType(), pp.getUnconnectedDrive(), pp.getTimeScale()};

    auto savedDefinitionKind = currentDefinitionKind;
    currentDefinitionKind = declKind;

    Token endmodule;
    auto members = parseMemberList<MemberSyntax>(
        endKind, endmodule, declKind, [this](SyntaxKind parentKind, bool& anyLocalModules) {
            return parseMember(parentKind, anyLocalModules);
        });

    currentDefinitionKind = savedDefinitionKind;
    pp.popDesignElementStack();

    auto endName = parseNamedBlockClause();
    checkBlockNames(header.name, endName);

    auto& result = factory.moduleDeclaration(declKind, attributes, header, members, endmodule,
                                             endName);

    meta.nodeMap[&result] = node;
    return result;
}

AnonymousProgramSyntax& Parser::parseAnonymousProgram(AttrList attributes) {
    auto& pp = getPP();
    pp.pushDesignElementStack();

    auto keyword = consume();
    auto semi = expect(TokenKind::Semicolon);

    Token endkeyword;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndProgramKeyword, endkeyword, SyntaxKind::AnonymousProgram,
        [this](SyntaxKind parentKind, bool& anyLocalModules) {
            return parseMember(parentKind, anyLocalModules);
        });

    pp.popDesignElementStack();

    return factory.anonymousProgram(attributes, keyword, semi, members, endkeyword);
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

    if (isHierarchyInstantiation(/* requireName */ false))
        return &parseHierarchyInstantiation(attributes);
    if (isPortDeclaration(/* inStatement */ false))
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
            if (!attributes.empty()) {
                return &factory.emptyMember(attributes, nullptr,
                                            Token::createMissing(alloc, TokenKind::Semicolon,
                                                                 token.location()));
            }

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
            return &parseSpecparam(attributes, parentKind);
        case TokenKind::AliasKeyword:
            return &parseNetAlias(attributes);
        case TokenKind::SpecifyKeyword:
            errorIfAttributes(attributes);
            return &parseSpecifyBlock(attributes);
        case TokenKind::Identifier:
            if (peek(1).kind == TokenKind::Colon) {
                // Declarations and instantiations have already been handled, so if we reach this
                // point we either have a labeled assertion, or this is some kind of error.
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

            // If there's a hash or parenthesis here this is likely a primitive instantiation.
            if (peek(1).kind == TokenKind::Hash || peek(1).kind == TokenKind::OpenParenthesis) {
                return &parsePrimitiveInstantiation(attributes);
            }

            // A double colon could be a package-scoped checker instantiation.
            if (peek(1).kind == TokenKind::DoubleColon && peek(2).kind == TokenKind::Identifier &&
                peek(3).kind == TokenKind::Identifier) {
                return &parseCheckerInstantiation(attributes);
            }

            // Otherwise, assume it's an (erroneous) attempt at a variable declaration.
            return &parseVariableDeclaration(attributes);
        case TokenKind::UnitSystemName: {
            // The only valid thing this can be is a checker instantiation, since
            // variable declarations would have been handled previously. Because these
            // are rare, disambiguate for a bit and then fall back to parsing as a
            // variable decl anyway for a better error message.
            if (peek(1).kind == TokenKind::DoubleColon && peek(2).kind == TokenKind::Identifier &&
                peek(3).kind == TokenKind::Identifier) {
                return &parseCheckerInstantiation(attributes);
            }
            return &parseVariableDeclaration(attributes);
        }
        case TokenKind::AssertKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::CoverKeyword: {
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
        case TokenKind::RestrictKeyword: {
            auto& statement = parseConcurrentAssertion(nullptr, {});
            return &factory.concurrentAssertionMember(
                attributes, statement.as<ConcurrentAssertionStatementSyntax>());
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
            return &parseCovergroupDeclaration(attributes, /* inClass */ false,
                                               /* hasBaseClass */ false);
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
            if (peek(1).kind == TokenKind::StringLiteral) {
                return &parseDPIExport(attributes);
            }
            return &parseExportDeclaration(attributes);
        case TokenKind::Semicolon:
            return &factory.emptyMember(attributes, nullptr, consume());
        case TokenKind::PropertyKeyword:
            return &parsePropertyDeclaration(attributes);
        case TokenKind::SequenceKeyword:
            return &parseSequenceDeclaration(attributes);
        case TokenKind::CheckerKeyword:
            return &parseCheckerDeclaration(attributes);
        case TokenKind::GlobalKeyword:
        case TokenKind::DefaultKeyword:
            if (peek(1).kind == TokenKind::ClockingKeyword) {
                return &parseClockingDeclaration(attributes);
            }
            else if (peek(1).kind == TokenKind::DisableKeyword &&
                     token.kind == TokenKind::DefaultKeyword) {
                return &parseDefaultDisable(attributes);
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
        case TokenKind::ConstraintKeyword:
            return &parseConstraint(attributes, {}, true);
        case TokenKind::PrimitiveKeyword:
            return &parseUdpDeclaration(attributes);
        case TokenKind::RandKeyword: {
            auto rand = consume();
            return &factory.checkerDataDeclaration(attributes, rand, parseDataDeclaration({}));
        }
        case TokenKind::ExternKeyword:
            errorIfAttributes(attributes);
            if (auto member = parseExternMember(parentKind, attributes))
                return member;
            break;
        case TokenKind::ConfigKeyword:
            errorIfAttributes(attributes);
            return &parseConfigDeclaration(attributes);
        default:
            break;
    }

    if (isGateType(token.kind))
        return &parsePrimitiveInstantiation(attributes);

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
            addDiag(diag::QualifiersOnOutOfBlock, token.range());
            for (uint32_t i = 0; i < index; i++)
                skipToken(std::nullopt);

            auto kind = t.kind == TokenKind::FunctionKeyword ? SyntaxKind::FunctionDeclaration
                                                             : SyntaxKind::TaskDeclaration;
            return &parseFunctionDeclaration(attributes, kind, getSkipToKind(t.kind), parentKind);
        }

        if (t.kind == TokenKind::ConstraintKeyword) {
            // Out-of-block constraints can legitimately have the 'static' keyword,
            // but nothing else.
            SmallVector<Token, 4> quals;
            for (uint32_t i = 0; i < index; i++) {
                Token qual = consume();
                quals.push_back(qual);

                if (qual.kind != TokenKind::StaticKeyword && isConstraintQualifier(qual.kind))
                    addDiag(diag::ConstraintQualOutOfBlock, qual.range()) << qual.valueText();
            }

            return &parseConstraint(attributes, quals.copy(alloc), true);
        }
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(attributes, nullptr,
                                    Token::createMissing(alloc, TokenKind::Semicolon,
                                                         token.location()));
    }

    // Otherwise, we got nothing and should just return null so that our
    // caller will skip and try again.
    return nullptr;
}

MemberSyntax* Parser::parseSingleMember(SyntaxKind parentKind) {
    bool anyLocalModules = false;
    auto result = parseMember(parentKind, anyLocalModules);
    if (anyLocalModules)
        moduleDeclStack.pop_back();

    if (result)
        checkMemberAllowed(*result, parentKind);

    return result;
}

template<typename TMember, typename TParseFunc>
std::span<TMember*> Parser::parseMemberList(TokenKind endKind, Token& endToken,
                                            SyntaxKind parentKind, TParseFunc&& parseFunc,
                                            uint32_t memberLimit) {
    SmallVector<TMember*, 8> members;
    bool errored = false;
    bool anyLocalModules = false;

    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || kind == endKind)
            break;

        auto member = parseFunc(parentKind, anyLocalModules);
        if (member) {
            // If memberLimit is set to 0 (which is default value)
            // the number of members will not be checked.
            if (memberLimit && memberLimit == members.size()) {
                addDiag(diag::MemberLimitViolation, member->sourceRange().start()) << memberLimit;
                continue;
            }

            checkMemberAllowed(*member, parentKind);
            members.push_back(member);
            errored = false;
        }
        else {
            if (isCloseDelimOrKeyword(kind)) {
                auto& diag = addDiag(diag::UnexpectedEndDelim, peek().range());
                diag << peek().valueText();
                errored = true;

                auto& lastBlock = getLastPoppedDelims();
                if (lastBlock.first && lastBlock.second) {
                    diag.addNote(diag::NoteLastBlockStarted, lastBlock.first.location());
                    diag.addNote(diag::NoteLastBlockEnded, lastBlock.second.location());
                }
            }

            skipToken(errored ? std::nullopt : std::make_optional(diag::ExpectedMember));
            errored = true;
        }
    }

    if (anyLocalModules)
        moduleDeclStack.pop_back();

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

    SmallVector<TokenOrSyntax, 8> buffer;
    while (true) {
        if (peek(TokenKind::FunctionKeyword) || peek(TokenKind::TaskKeyword)) {
            auto& proto = parseFunctionPrototype(SyntaxKind::Unknown,
                                                 FunctionOptions::AllowEmptyArgNames |
                                                     FunctionOptions::IsPrototype);
            buffer.push_back(&factory.modportSubroutinePort(proto));
        }
        else {
            auto name = expect(TokenKind::Identifier);
            buffer.push_back(&factory.modportNamedPort(name));
            if (name.isMissing())
                break;
        }

        if (!peek(TokenKind::Comma) ||
            (peek(1).kind != TokenKind::FunctionKeyword && peek(1).kind != TokenKind::TaskKeyword &&
             peek(1).kind != TokenKind::Identifier)) {
            break;
        }

        buffer.push_back(consume());
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

    SmallVector<TokenOrSyntax, 8> buffer;
    while (true) {
        if (peek(TokenKind::Dot)) {
            auto dot = consume();
            auto name = expect(TokenKind::Identifier);
            auto openParen = expect(TokenKind::OpenParenthesis);

            ExpressionSyntax* expr = nullptr;
            if (!peek(TokenKind::CloseParenthesis))
                expr = &parseExpression();

            buffer.push_back(&factory.modportExplicitPort(dot, name, openParen, expr,
                                                          expect(TokenKind::CloseParenthesis)));
        }
        else {
            auto name = expect(TokenKind::Identifier);
            buffer.push_back(&factory.modportNamedPort(name));
            if (name.isMissing())
                break;
        }

        if (!peek(TokenKind::Comma) ||
            (peek(1).kind != TokenKind::Dot && peek(1).kind != TokenKind::Identifier)) {
            break;
        }

        buffer.push_back(consume());
    }

    return factory.modportSimplePortList(attributes, direction, buffer.copy(alloc));
}

ModportItemSyntax& Parser::parseModportItem() {
    auto name = expect(TokenKind::Identifier);

    Token openParen, closeParen;
    std::span<TokenOrSyntax> items;
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
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isIdentifierOrComma, isSemicolon>(buffer, TokenKind::Semicolon, TokenKind::Comma,
                                                semi, RequireItems::True, diag::ExpectedIdentifier,
                                                [this] { return &parseModportItem(); });

    return factory.modportDeclaration(attributes, keyword, buffer.copy(alloc), semi);
}

FunctionPortBaseSyntax& Parser::parseFunctionPort(bitmask<FunctionOptions> options) {
    if (peek(TokenKind::DefaultKeyword)) {
        auto keyword = consume();
        if (!options.has(FunctionOptions::AllowDefaultArg)) {
            addDiag(diag::DefaultArgNotAllowed, keyword.range());
        }
        else if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, keyword.range())
                << toString(parseOptions.languageVersion);
        }
        return factory.defaultFunctionPort(keyword);
    }

    auto attributes = parseAttributes();
    auto constKeyword = consumeIf(TokenKind::ConstKeyword);

    Token direction;
    if (isPortDirection(peek().kind))
        direction = consume();

    if (constKeyword && direction.kind != TokenKind::RefKeyword) {
        auto location = direction ? direction.location() : constKeyword.location();
        addDiag(diag::ConstFunctionPortRequiresRef, location);
    }

    Token staticKeyword;
    if (direction.kind == TokenKind::RefKeyword && peek(TokenKind::StaticKeyword)) {
        staticKeyword = consume();
        if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, staticKeyword.range())
                << toString(parseOptions.languageVersion);
        }
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
    if (!options.has(FunctionOptions::AllowEmptyArgNames) || peek(TokenKind::Identifier) ||
        peek(TokenKind::Equals)) {
        decl = &parseDeclarator();
    }
    else {
        decl = &factory.declarator(placeholderToken(), nullptr, nullptr);
    }
    return factory.functionPort(attributes, constKeyword, direction, staticKeyword, varKeyword,
                                dataType, *decl);
}

static bool checkSubroutineName(const NameSyntax& name) {
    auto checkKind = [](auto& node) {
        return node.kind == SyntaxKind::IdentifierName || node.kind == SyntaxKind::ConstructorName;
    };

    if (name.kind == SyntaxKind::ScopedName) {
        auto& scoped = name.as<ScopedNameSyntax>();
        return checkKind(*scoped.left) && checkKind(*scoped.right);
    }

    return checkKind(name);
}

FunctionPortListSyntax* Parser::parseFunctionPortList(bitmask<FunctionOptions> options) {
    if (!peek(TokenKind::OpenParenthesis))
        return nullptr;

    auto openParen = consume();
    Token closeParen;
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleFunctionPort, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
        diag::ExpectedFunctionPort, [this, options] { return &parseFunctionPort(options); });

    return &factory.functionPortList(openParen, buffer.copy(alloc), closeParen);
}

FunctionPrototypeSyntax& Parser::parseFunctionPrototype(SyntaxKind parentKind,
                                                        bitmask<FunctionOptions> options,
                                                        bool* isConstructor) {
    Token keyword;
    if (peek(TokenKind::TaskKeyword))
        keyword = consume();
    else
        keyword = expect(TokenKind::FunctionKeyword);

    auto specifiers = parseClassSpecifierList(
        options.has(FunctionOptions::AllowOverrideSpecifiers));

    auto lifetime = parseLifetime();
    if (lifetime && options.has(FunctionOptions::IsPrototype))
        addDiag(diag::LifetimeForPrototype, lifetime.range());

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
            returnType = &factory.implicitType(Token(), nullptr, placeholderToken());
    }

    auto& name = parseName();
    if (!checkSubroutineName(name))
        addDiag(diag::ExpectedSubroutineName, keyword.location()) << name.sourceRange();

    if (options.has(FunctionOptions::IsPrototype) && name.kind == SyntaxKind::ScopedName) {
        addDiag(diag::SubroutinePrototypeScoped, name.getFirstToken().location());
    }
    else if (lifetime.kind == TokenKind::StaticKeyword && name.kind == SyntaxKind::ScopedName &&
             name.as<ScopedNameSyntax>().separator.kind == TokenKind::DoubleColon) {
        addDiag(diag::MethodStaticLifetime, lifetime.range());
    }

    bool constructor = getLastConsumed().kind == TokenKind::NewKeyword;
    if (isConstructor)
        *isConstructor = constructor;

    if (constructor)
        options |= FunctionOptions::AllowDefaultArg;

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

    auto portList = parseFunctionPortList(options);
    return factory.functionPrototype(keyword, specifiers, lifetime, *returnType, name, portList);
}

FunctionDeclarationSyntax& Parser::parseFunctionDeclaration(AttrList attributes,
                                                            SyntaxKind functionKind,
                                                            TokenKind endKind,
                                                            SyntaxKind parentKind,
                                                            bitmask<FunctionOptions> options) {
    Token end;
    bool isConstructor;
    auto& prototype = parseFunctionPrototype(parentKind,
                                             options | FunctionOptions::AllowImplicitReturn,
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
    std::span<TokenOrSyntax> identifiers;

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
            addDiag(diag::InvalidGenvarIterExpression, iterationExpr->sourceRange());
            iterationExpr = &factory.badExpression(*iterationExpr);
            break;
    }

    // Make sure the iteration expression only mentions the genvar on the lhs.
    if (iterVarCheck && !identifier.isMissing() &&
        (iterVarCheck->kind != SyntaxKind::IdentifierName ||
         iterVarCheck->as<IdentifierNameSyntax>().identifier.valueText() !=
             identifier.valueText())) {

        addDiag(diag::ExpectedGenvarIterVar, iterVarCheck->sourceRange());
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

    SmallVector<CaseItemSyntax*> itemBuffer;
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
            itemBuffer.push_back(&factory.defaultCaseItem(def, colon, parseGenerateBlock()));
        }
        else if (isPossibleExpression(kind)) {
            Token colon;
            SmallVector<TokenOrSyntax, 8> buffer;
            parseList<isPossibleExpressionOrComma, isEndOfCaseItem>(
                buffer, TokenKind::Colon, TokenKind::Comma, colon, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });
            itemBuffer.push_back(
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
            auto loc = peek().location();
            addDiag(diag::ExpectedMember, loc);
            return factory.emptyMember(nullptr, nullptr, missingToken(TokenKind::Semicolon, loc));
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
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrComma, isSemicolon>(buffer, TokenKind::Semicolon,
                                                        TokenKind::Comma, semi, RequireItems::True,
                                                        diag::ExpectedInterfaceClassName,
                                                        [this] { return &parseName(); });

    return &factory.implementsClause(implements, buffer.copy(alloc));
}

ClassSpecifierSyntax* Parser::parseClassSpecifier() {
    if (peek(TokenKind::Colon)) {
        auto colon = consume();

        Token keyword;
        switch (peek().kind) {
            case TokenKind::InitialKeyword:
            case TokenKind::ExtendsKeyword:
            case TokenKind::FinalKeyword:
                keyword = consume();
                break;
            default:
                skipToken(diag::ExpectedClassSpecifier);
                break;
        }

        auto& result = factory.classSpecifier(colon, keyword);
        if (parseOptions.languageVersion < LanguageVersion::v1800_2023 && keyword) {
            addDiag(diag::WrongLanguageVersion, result.sourceRange())
                << toString(parseOptions.languageVersion);
        }

        return &result;
    }
    return nullptr;
}

std::span<syntax::ClassSpecifierSyntax*> Parser::parseClassSpecifierList(bool allowSpecifiers) {
    bool erroredOnFinal = false;
    SmallVector<ClassSpecifierSyntax*> specifiers;
    while (peek(TokenKind::Colon)) {
        auto specifier = parseClassSpecifier();
        SLANG_ASSERT(specifier);

        if (!specifier->keyword.isMissing()) {
            if (specifiers.empty() && !allowSpecifiers)
                addDiag(diag::SpecifiersNotAllowed, specifier->sourceRange());

            for (auto other : specifiers) {
                const auto sk = specifier->keyword;
                const auto ok = other->keyword;

                if (sk.kind == ok.kind) {
                    addDiag(diag::DuplicateClassSpecifier, sk.range())
                        << sk.valueText() << ok.range();
                    break;
                }

                if (ok.kind == TokenKind::FinalKeyword && !erroredOnFinal) {
                    erroredOnFinal = true;
                    addDiag(diag::FinalSpecifierLast, ok.range());
                    break;
                }

                if (!ok.isMissing() && ok.kind != TokenKind::FinalKeyword &&
                    sk.kind != TokenKind::FinalKeyword) {
                    addDiag(diag::ClassSpecifierConflict, sk.range())
                        << sk.valueText() << ok.range() << ok.valueText();
                    break;
                }
            }
        }

        specifiers.push_back(specifier);
    }

    return specifiers.copy(alloc);
}

ClassDeclarationSyntax& Parser::parseClassDeclaration(AttrList attributes,
                                                      Token virtualOrInterface) {
    auto classKeyword = consume();

    const bool isIfaceClass = virtualOrInterface.kind == TokenKind::InterfaceKeyword;
    ClassSpecifierSyntax* finalSpecifier = nullptr;
    if (!isIfaceClass) {
        auto next = peek();
        if (next.kind == TokenKind::StaticKeyword || next.kind == TokenKind::AutomaticKeyword) {
            // This was allowed in 1800-2017 but did nothing, so silently skip it.
            // It was removed in 1800-2023 so issue an error.
            if (parseOptions.languageVersion < LanguageVersion::v1800_2023)
                skipToken({});
            else
                skipToken(diag::ExpectedIdentifier);
            next = peek();
        }

        finalSpecifier = parseClassSpecifier();
        if (finalSpecifier && finalSpecifier->keyword &&
            finalSpecifier->keyword.kind != TokenKind::FinalKeyword) {
            addDiag(diag::ExpectedToken, finalSpecifier->keyword.location()) << "final"sv;
        }
    }

    auto name = expect(TokenKind::Identifier);
    auto parameterList = parseParameterPortList();

    Token semi;
    ExtendsClauseSyntax* extendsClause = nullptr;
    ImplementsClauseSyntax* implementsClause = nullptr;

    // interface classes treat "extends" as the implements list
    if (isIfaceClass) {
        implementsClause = parseImplementsClause(TokenKind::ExtendsKeyword, semi);
    }
    else {
        if (peek(TokenKind::ExtendsKeyword)) {
            auto extends = consume();
            auto& baseName = parseName();

            ArgumentListSyntax* arguments = nullptr;
            DefaultExtendsClauseArgSyntax* defaultedArg = nullptr;
            if (peek(TokenKind::OpenParenthesis)) {
                if (peek(1).kind == TokenKind::DefaultKeyword) {
                    auto openParen = consume();
                    auto defaultKeyword = consume();
                    defaultedArg = &factory.defaultExtendsClauseArg(
                        openParen, defaultKeyword, expect(TokenKind::CloseParenthesis));

                    if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
                        addDiag(diag::WrongLanguageVersion, defaultedArg->sourceRange())
                            << toString(parseOptions.languageVersion);
                    }
                }
                else {
                    arguments = &parseArgumentList();
                }
            }

            extendsClause = &factory.extendsClause(extends, baseName, arguments, defaultedArg);
        }
        implementsClause = parseImplementsClause(TokenKind::ImplementsKeyword, semi);
    }

    Token endClass;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndClassKeyword, endClass, SyntaxKind::ClassDeclaration,
        [this, isIfaceClass, extendsClause](SyntaxKind, bool&) {
            return parseClassMember(isIfaceClass, extendsClause != nullptr);
        });

    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    auto& result = factory.classDeclaration(attributes, virtualOrInterface, classKeyword,
                                            finalSpecifier, name, parameterList, extendsClause,
                                            implementsClause, semi, members, endClass,
                                            endBlockName);
    meta.classDecls.push_back(&result);
    return result;
}

void Parser::checkClassQualifiers(std::span<const Token> qualifiers, bool isConstraint) {
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
                    auto& diag = addDiag(diag::QualifierConflict, curr.range());
                    diag << curr.rawText();
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
                auto& diag = addDiag(diag::DuplicateQualifier, t.range());
                diag << t.rawText() << it->second.range();
                errorDup = true;
            }
            continue;
        }

        // Some qualifiers are required to come first in the list.
        if (count > 1 && (t.kind == TokenKind::PureKeyword || t.kind == TokenKind::ExternKeyword)) {
            if (!errorFirst) {
                auto& diag = addDiag(diag::QualifierNotFirst, t.range());
                diag << t.rawText();
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
                    auto& diag = addDiag(diag::PureRequiresVirtual, t.range());
                    diag << lastPure.range();
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
        addDiag(diag::PureRequiresVirtual, lastPure.range());
}

MemberSyntax* Parser::parseClassMember(bool isIfaceClass, bool hasBaseClass) {
    auto errorIfIface = [&](const SyntaxNode& syntax) {
        if (isIfaceClass)
            addDiag(diag::NotAllowedInIfaceClass, syntax.sourceRange());
    };

    auto attributes = parseAttributes();

    // virtual keyword can either be a class decl, virtual interface, or a method qualifier.
    // Early out here if it's a class.
    if (peek(TokenKind::VirtualKeyword) && peek(1).kind == TokenKind::ClassKeyword) {
        auto& result = parseClassDeclaration(attributes, consume());
        errorIfIface(result);
        return &result;
    }

    bool isPureOrExtern = false;
    SmallVector<Token, 4> qualifierBuffer;
    while (isMemberQualifier(peek().kind)) {
        // As mentioned above, the virtual keyword needs special handling
        // because it might be a virtual method or a virtual interface property.
        if (peek(TokenKind::VirtualKeyword) && !isPureOrExtern) {
            // If the next token after this is another qualifier or a method
            // keyword then we should take it; otherwise assume that it will
            // be parsed as a variable declaration.
            auto kind = peek(1).kind;
            if (!isMemberQualifier(kind) && kind != TokenKind::FunctionKeyword &&
                kind != TokenKind::TaskKeyword) {
                break;
            }
        }

        Token t = consume();
        qualifierBuffer.push_back(t);
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
                auto& diag = addDiag(diag::InvalidPropertyQualifier, qual.range());
                diag << qual.rawText();
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
                        auto& diag = addDiag(diag::DuplicateQualifier, mod.range());
                        diag << mod.rawText() << lastLifetime.range();
                    }
                    else {
                        auto& diag = addDiag(diag::QualifierConflict, mod.range());
                        diag << mod.rawText();
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
            addDiag(diag::NotAllowedInClass, decl.sourceRange());
        }
        else {
            // Otherwise, check for invalid qualifiers.
            for (auto qual : qualifiers) {
                if (isIfaceClass) {
                    addDiag(diag::InvalidQualifierForIfaceMember, qual.range());
                    break;
                }

                switch (qual.kind) {
                    case TokenKind::RandKeyword:
                    case TokenKind::RandCKeyword:
                    case TokenKind::ConstKeyword:
                    case TokenKind::StaticKeyword:
                        addDiag(diag::InvalidQualifierForMember, qual.range());
                        break;
                    case TokenKind::LocalKeyword:
                    case TokenKind::ProtectedKeyword:
                        if (decl.kind == SyntaxKind::ParameterDeclarationStatement)
                            addDiag(diag::InvalidQualifierForMember, qual.range());
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
        bool isStatic = false;
        for (auto qual : qualifiers) {
            if (qual.kind == TokenKind::PureKeyword)
                isPure = true;
            else if (qual.kind == TokenKind::StaticKeyword)
                isStatic = true;

            if (!isMethodQualifier(qual.kind)) {
                auto& diag = addDiag(diag::InvalidMethodQualifier, qual.range());
                diag << qual.rawText();
                break;
            }

            if (isIfaceClass && qual.kind != TokenKind::PureKeyword &&
                qual.kind != TokenKind::VirtualKeyword) {
                addDiag(diag::InvalidQualifierForIfaceMember, qual.range());
                isPure = true;
                break;
            }
        }

        if (isIfaceClass && !isPure)
            addDiag(diag::IfaceMethodPure, peek().location());

        auto checkProto = [&](auto& proto, bool checkLifetime) {
            if (checkLifetime && proto.lifetime.kind == TokenKind::StaticKeyword)
                addDiag(diag::MethodStaticLifetime, proto.lifetime.range());

            // Specifiers are not allowed on static methods.
            if (isStatic && !proto.specifiers.empty())
                addDiag(diag::StaticFuncSpecifier, proto.specifiers[0]->sourceRange());

            // If there's no base class it can't be marked `extends`.
            auto lastNamePart = proto.name->getLastToken();
            if (!hasBaseClass) {
                for (auto specifier : proto.specifiers) {
                    if (specifier->keyword.kind == TokenKind::ExtendsKeyword) {
                        auto name = lastNamePart.valueText();
                        if (!name.empty())
                            addDiag(diag::OverridingExtends, specifier->sourceRange()) << name;
                        break;
                    }
                }
            }

            // Additional checking for constructors.
            if (lastNamePart.kind == TokenKind::NewKeyword) {
                for (auto qual : qualifiers) {
                    if (qual.kind == TokenKind::VirtualKeyword ||
                        qual.kind == TokenKind::StaticKeyword) {
                        addDiag(diag::InvalidQualifierForConstructor, qual.range());
                        break;
                    }
                }
            }
        };

        bitmask<FunctionOptions> funcOptions;
        if (!isIfaceClass)
            funcOptions = FunctionOptions::AllowOverrideSpecifiers;

        // Pure or extern functions don't have bodies.
        if (isPureOrExtern) {
            auto& proto = parseFunctionPrototype(SyntaxKind::ClassDeclaration,
                                                 funcOptions | FunctionOptions::IsPrototype);
            checkProto(proto, false);

            // Final specifier is illegal on pure virtual methods.
            if (isPure) {
                for (auto specifier : proto.specifiers) {
                    if (specifier->keyword.kind == TokenKind::FinalKeyword) {
                        addDiag(diag::FinalWithPure, specifier->sourceRange());
                        break;
                    }
                }
            }

            return &factory.classMethodPrototype(attributes, qualifiers, proto,
                                                 expect(TokenKind::Semicolon));
        }
        else {
            auto declKind = kind == TokenKind::TaskKeyword ? SyntaxKind::TaskDeclaration
                                                           : SyntaxKind::FunctionDeclaration;
            auto endKind = kind == TokenKind::TaskKeyword ? TokenKind::EndTaskKeyword
                                                          : TokenKind::EndFunctionKeyword;
            auto& funcDecl = parseFunctionDeclaration({}, declKind, endKind,
                                                      SyntaxKind::ClassDeclaration, funcOptions);
            checkProto(*funcDecl.prototype, true);

            // If this is a scoped name, it should be an out-of-block definition for
            // a method declared in a nested class. Qualifiers are not allowed here.
            if (funcDecl.prototype->name->kind == SyntaxKind::ScopedName && !qualifiers.empty()) {
                addDiag(diag::QualifiersOnOutOfBlock, qualifiers[0].range());
            }

            return &factory.classMethodDeclaration(attributes, qualifiers, funcDecl);
        }
    }

    if (kind == TokenKind::ConstraintKeyword) {
        auto& result = parseConstraint(attributes, qualifiers, hasBaseClass);
        errorIfIface(result);
        return &result;
    }

    // Qualifiers aren't allowed past this point, so return an empty member to hold them.
    if (!qualifiers.empty()) {
        addDiag(diag::UnexpectedQualifiers, qualifiers[0].location());
        return &factory.emptyMember(attributes, qualifiers,
                                    Token::createMissing(alloc, TokenKind::Semicolon,
                                                         peek().location()));
    }

    switch (kind) {
        case TokenKind::ClassKeyword: {
            auto& result = parseClassDeclaration(attributes, Token());
            errorIfIface(result);
            return &result;
        }
        case TokenKind::CoverGroupKeyword: {
            auto& result = parseCovergroupDeclaration(attributes, /* inClass */ true, hasBaseClass);
            errorIfIface(result);
            return &result;
        }
        case TokenKind::Semicolon:
            errorIfAttributes(attributes);
            return &factory.emptyMember(attributes, qualifiers, consume());
        case TokenKind::InterfaceKeyword:
            if (peek(1).kind == TokenKind::ClassKeyword) {
                if (isIfaceClass || parseOptions.languageVersion < LanguageVersion::v1800_2023)
                    addDiag(diag::NestedIface, peek().location());
                return &parseClassDeclaration(attributes, consume());
            }
            break;
        default:
            break;
    }

    // If we got attributes but don't know what comes next, we have some kind of nonsense.
    if (!attributes.empty()) {
        return &factory.emptyMember(attributes, qualifiers,
                                    Token::createMissing(alloc, TokenKind::Semicolon,
                                                         peek().location()));
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
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedContinuousAssignment, [this] {
            auto& expr = parseExpression();
            if (expr.kind != SyntaxKind::AssignmentExpression)
                addDiag(diag::ExpectedContinuousAssignment, expr.sourceRange());
            return &expr;
        });

    return factory.continuousAssign(attributes, assign, strength, delay, buffer.copy(alloc), semi);
}

DefParamAssignmentSyntax& Parser::parseDefParamAssignment() {
    auto& name = parseName();
    auto equals = expect(TokenKind::Equals);
    auto& init = factory.equalsValueClause(equals, parseMinTypMaxExpression());
    return factory.defParamAssignment(name, init);
}

DefParamSyntax& Parser::parseDefParam(AttrList attributes) {
    auto defparam = consume();

    Token semi;
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrComma, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
        diag::ExpectedVariableAssignment, [this] { return &parseDefParamAssignment(); });

    meta.hasDefparams = true;
    return factory.defParam(attributes, defparam, buffer.copy(alloc), semi);
}

static bool isValidOption(const ExpressionSyntax& expr) {
    if (expr.kind != SyntaxKind::AssignmentExpression)
        return false;

    auto& assign = expr.as<BinaryExpressionSyntax>();
    if (assign.left->kind != SyntaxKind::ScopedName)
        return false;

    auto& scoped = assign.left->as<ScopedNameSyntax>();
    if (scoped.left->kind != SyntaxKind::IdentifierName ||
        scoped.right->kind != SyntaxKind::IdentifierName) {
        return false;
    }

    return true;
}

CoverageOptionSyntax* Parser::parseCoverageOption(AttrList attributes) {
    auto token = peek();
    if (token.kind == TokenKind::Identifier) {
        if (token.valueText() == "option" || token.valueText() == "type_option") {
            auto& expr = parseExpression();
            if (!isValidOption(expr))
                addDiag(diag::InvalidCoverageOption, expr.sourceRange());

            return &factory.coverageOption(attributes, expr, expect(TokenKind::Semicolon));
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
        if (peek(TokenKind::CrossKeyword))
            return parseCoverCross(attributes, &label);
        else
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
        case TokenKind::CrossKeyword:
            return parseCoverCross(attributes, nullptr);
        default:
            break;
    }

    // if we got attributes but don't know what comes next, we have some kind of nonsense
    if (!attributes.empty()) {
        return &factory.emptyMember(attributes, nullptr,
                                    Token::createMissing(alloc, TokenKind::Semicolon,
                                                         peek().location()));
    }

    // otherwise, we got nothing and should just return null so that our caller will skip and try
    // again.
    return nullptr;
}

CoverageIffClauseSyntax* Parser::parseCoverageIffClause() {
    if (!peek(TokenKind::IffKeyword))
        return nullptr;

    auto iff = consume();
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto& expr = parseExpression();
    return &factory.coverageIffClause(iff, openParen, expr, expect(TokenKind::CloseParenthesis));
}

CoverpointSyntax* Parser::parseCoverpoint(AttrList attributes, DataTypeSyntax* type,
                                          NamedLabelSyntax* label) {
    auto keyword = expect(TokenKind::CoverPointKeyword);
    auto& expr = parseExpression();
    auto iff = parseCoverageIffClause();

    if (!type)
        type = &factory.implicitType(Token(), nullptr, placeholderToken());

    if (peek(TokenKind::OpenBrace)) {
        auto openBrace = consume();

        Token closeBrace;
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::CloseBrace, closeBrace, SyntaxKind::Coverpoint,
            [this](SyntaxKind, bool&) { return parseCoverpointMember(); });

        return &factory.coverpoint(attributes, *type, label, keyword, expr, iff, openBrace, members,
                                   closeBrace, Token());
    }

    // no brace, so this is an empty list, expect a semicolon
    return &factory.coverpoint(attributes, *type, label, keyword, expr, iff, Token(), nullptr,
                               Token(), expect(TokenKind::Semicolon));
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

    // error out if we have total junk here
    if (!wildcard && !bins && attributes.empty())
        return nullptr;

    Token name = expect(TokenKind::Identifier);

    CoverageBinsArraySizeSyntax* size = nullptr;
    if (peek(TokenKind::OpenBracket)) {
        auto openBracket = consume();

        ExpressionSyntax* expr = nullptr;
        if (!peek(TokenKind::CloseBracket))
            expr = &parseExpression();

        size = &factory.coverageBinsArraySize(openBracket, expr, expect(TokenKind::CloseBracket));
    }

    // bunch of different kinds of initializers here
    CoverageBinInitializerSyntax* initializer = nullptr;
    Token equals = expect(TokenKind::Equals);

    switch (peek().kind) {
        case TokenKind::OpenBrace: {
            auto& ranges = parseRangeList();
            auto with = parseWithClause();
            initializer = &factory.rangeCoverageBinInitializer(ranges, with);
            break;
        }
        case TokenKind::DefaultKeyword: {
            auto defaultKeyword = consume();
            auto sequenceKeyword = consumeIf(TokenKind::SequenceKeyword);
            initializer = &factory.defaultCoverageBinInitializer(defaultKeyword, sequenceKeyword);

            if (wildcard) {
                addDiag(diag::CoverageBinDefaultWildcard, wildcard.location())
                    << defaultKeyword.range();
            }

            if (sequenceKeyword && size) {
                addDiag(diag::CoverageBinDefSeqSize, sequenceKeyword.location())
                    << size->sourceRange();
            }

            if (bins.kind == TokenKind::IgnoreBinsKeyword) {
                addDiag(diag::CoverageBinDefaultIgnore, defaultKeyword.location()) << bins.range();
            }
            break;
        }
        case TokenKind::OpenParenthesis:
            if (size && size->expr)
                addDiag(diag::CoverageBinTransSize, size->expr->sourceRange());

            initializer = &parseTransListInitializer();
            break;
        case TokenKind::Identifier:
            if (peek(1).kind == TokenKind::WithKeyword) {
                auto id = consume();
                auto with = parseWithClause();
                SLANG_ASSERT(with);
                initializer = &factory.idWithExprCoverageBinInitializer(id, *with);
                break;
            }
            [[fallthrough]];
        default: {
            auto& expr = parseExpression();
            initializer = &factory.expressionCoverageBinInitializer(expr);
            break;
        }
    }

    auto iff = parseCoverageIffClause();
    return &factory.coverageBins(attributes, wildcard, bins, name, size, equals, *initializer, iff,
                                 expect(TokenKind::Semicolon));
}

TransRangeSyntax& Parser::parseTransRange() {
    SmallVector<TokenOrSyntax, 8> buffer;
    while (true) {
        buffer.push_back(&parseValueRangeElement(ExpressionOptions::SequenceExpr));
        if (!peek(TokenKind::Comma))
            break;

        buffer.push_back(consume());
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

        SelectorSyntax* selector = parseSequenceRange();
        repeat = &factory.transRepeatRange(openBracket, specifier, selector,
                                           expect(TokenKind::CloseBracket));
    }

    return factory.transRange(buffer.copy(alloc), repeat);
}

TransSetSyntax& Parser::parseTransSet() {
    Token openParen;
    Token closeParen;
    std::span<TokenOrSyntax> list;

    parseList<isPossibleTransSet, isEndOfTransSet>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::EqualsArrow, openParen,
        list, closeParen, RequireItems::True, diag::ExpectedExpression,
        [this] { return &parseTransRange(); });

    return factory.transSet(openParen, list, closeParen);
}

TransListCoverageBinInitializerSyntax& Parser::parseTransListInitializer() {
    SmallVector<TokenOrSyntax, 8> buffer;
    while (true) {
        buffer.push_back(&parseTransSet());
        if (!peek(TokenKind::Comma))
            break;

        buffer.push_back(consume());
    }

    return factory.transListCoverageBinInitializer(buffer.copy(alloc));
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

CoverCrossSyntax* Parser::parseCoverCross(AttrList attributes, NamedLabelSyntax* label) {
    auto keyword = expect(TokenKind::CrossKeyword);

    SmallVector<TokenOrSyntax, 8> buffer;
    while (true) {
        auto name = expect(TokenKind::Identifier);
        buffer.push_back(&factory.identifierName(name));
        if (!peek(TokenKind::Comma))
            break;

        buffer.push_back(consume());
    }

    if (buffer.size() < 2)
        addDiag(diag::CoverCrossItems, peek().location());

    auto iff = parseCoverageIffClause();

    if (peek(TokenKind::OpenBrace)) {
        auto openBrace = consume();

        Token closeBrace;
        auto members = parseMemberList<MemberSyntax>(
            TokenKind::CloseBrace, closeBrace, SyntaxKind::CoverCross,
            [this](SyntaxKind, bool&) { return parseCoverCrossMember(); });

        return &factory.coverCross(attributes, label, keyword, buffer.copy(alloc), iff, openBrace,
                                   members, closeBrace, Token());
    }

    // no brace, so this is an empty list, expect a semicolon
    return &factory.coverCross(attributes, label, keyword, buffer.copy(alloc), iff, Token(),
                               nullptr, Token(), expect(TokenKind::Semicolon));
}

BinsSelectExpressionSyntax& Parser::parseBinsSelectPrimary() {
    auto parseCondition = [&]() -> BinsSelectConditionExprSyntax& {
        auto binsof = expect(TokenKind::BinsOfKeyword);
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& name = parseName();
        auto closeParen = expect(TokenKind::CloseParenthesis);

        IntersectClauseSyntax* intersectClause = nullptr;
        if (peek(TokenKind::IntersectKeyword)) {
            auto intersect = consume();
            auto& ranges = parseRangeList();
            intersectClause = &factory.intersectClause(intersect, ranges);
        }

        return factory.binsSelectConditionExpr(binsof, openParen, name, closeParen,
                                               intersectClause);
    };

    auto parseMatches = [&] {
        MatchesClauseSyntax* matchesClause = nullptr;
        if (peek(TokenKind::MatchesKeyword)) {
            auto matches = consume();
            auto& matchExpr = parseSubExpression(ExpressionOptions::BinsSelectContext, 0);
            matchesClause = &factory.matchesClause(matches, factory.expressionPattern(matchExpr));
        }
        return matchesClause;
    };

    BinsSelectExpressionSyntax* result;
    switch (peek().kind) {
        case TokenKind::BinsOfKeyword:
            result = &parseCondition();
            break;
        case TokenKind::Exclamation: {
            auto op = consume();
            result = &factory.unaryBinsSelectExpr(op, parseCondition());
            break;
        }
        case TokenKind::OpenParenthesis: {
            auto openParen = consume();
            auto& expr = parseBinsSelectExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            result = &factory.parenthesizedBinsSelectExpr(openParen, expr, closeParen);
            break;
        }
        default: {
            auto& expr = parseSubExpression(ExpressionOptions::BinsSelectContext, 0);
            auto matches = parseMatches();
            result = &factory.simpleBinsSelectExpr(expr, matches);
            break;
        }
    }

    if (peek(TokenKind::WithKeyword)) {
        auto with = consume();
        auto openParen = expect(TokenKind::OpenParenthesis);
        auto& expr = parseExpression();
        auto closeParen = expect(TokenKind::CloseParenthesis);
        auto matches = parseMatches();
        result = &factory.binSelectWithFilterExpr(*result, with, openParen, expr, closeParen,
                                                  matches);
    }

    return *result;
}

BinsSelectExpressionSyntax& Parser::parseBinsSelectExpression() {
    auto curr = &parseBinsSelectPrimary();
    while (peek(TokenKind::DoubleAnd) || peek(TokenKind::DoubleOr)) {
        auto op = consume();
        curr = &factory.binaryBinsSelectExpr(*curr, op, parseBinsSelectPrimary());
    }
    return *curr;
}

MemberSyntax* Parser::parseCoverCrossMember() {
    auto attributes = parseAttributes();

    if (peek(TokenKind::FunctionKeyword)) {
        return &parseFunctionDeclaration(attributes, SyntaxKind::FunctionDeclaration,
                                         TokenKind::EndFunctionKeyword, SyntaxKind::CoverCross);
    }

    // check for coverage option
    auto option = parseCoverageOption(attributes);
    if (option)
        return option;

    Token bins;
    switch (peek().kind) {
        case TokenKind::BinsKeyword:
        case TokenKind::IllegalBinsKeyword:
        case TokenKind::IgnoreBinsKeyword:
            bins = consume();
            break;
        default:
            break;
    }

    // error out if we have total junk here
    if (!bins && attributes.empty())
        return nullptr;

    auto name = expect(TokenKind::Identifier);
    auto equals = expect(TokenKind::Equals);
    auto& expr = parseBinsSelectExpression();
    auto iff = parseCoverageIffClause();

    return &factory.binsSelection(attributes, bins, name, equals, expr, iff,
                                  expect(TokenKind::Semicolon));
}

CovergroupDeclarationSyntax& Parser::parseCovergroupDeclaration(AttrList attributes, bool inClass,
                                                                bool hasBaseClass) {
    auto keyword = consume();
    auto extends = consumeIf(TokenKind::ExtendsKeyword);
    auto name = expect(TokenKind::Identifier);
    auto portList = parseFunctionPortList({});

    SyntaxNode* event = nullptr;
    switch (peek().kind) {
        case TokenKind::At: {
            auto at = consume();
            event = &factory.eventControlWithExpression(at, parseEventExpression());
            break;
        }
        case TokenKind::DoubleAt: {
            auto atat = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& expr = parseBlockEventExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            event = &factory.blockCoverageEvent(atat, openParen, expr, closeParen);
            break;
        }
        case TokenKind::WithKeyword: {
            auto with = consume();
            auto function = expect(TokenKind::FunctionKeyword);

            auto sample = expect(TokenKind::Identifier);
            if (!sample.isMissing() && sample.valueText() != "sample"sv)
                addDiag(diag::ExpectedSampleKeyword, sample.location());

            auto samplePortList = parseFunctionPortList({});
            if (!samplePortList)
                addDiag(diag::ExpectedFunctionPortList, peek().location());

            event = &factory.withFunctionSample(with, function, sample, samplePortList);
            break;
        }
        default:
            break;
    }

    if (extends) {
        if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, extends.range())
                << toString(parseOptions.languageVersion);
        }

        if (portList)
            addDiag(diag::ExpectedToken, portList->getFirstToken().location()) << ";"sv;
        if (event)
            addDiag(diag::ExpectedToken, event->getFirstToken().location()) << ";"sv;

        if (!inClass)
            addDiag(diag::DerivedCovergroupNotInClass, extends.range());
        else if (!hasBaseClass)
            addDiag(diag::DerivedCovergroupNoBase, extends.range());
    }

    auto semi = expect(TokenKind::Semicolon);

    Token endGroup;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndGroupKeyword, endGroup, SyntaxKind::CovergroupDeclaration,
        [this](SyntaxKind, bool&) { return parseCoverageMember(); });

    auto endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.covergroupDeclaration(attributes, keyword, extends, name, portList, event, semi,
                                         members, endGroup, endBlockName);
}

static bool checkConstraintName(const NameSyntax& name) {
    if (name.kind == SyntaxKind::ScopedName) {
        auto& scoped = name.as<ScopedNameSyntax>();
        if (scoped.separator.kind == TokenKind::Dot)
            return false;

        return scoped.left->kind == SyntaxKind::IdentifierName &&
               scoped.right->kind == SyntaxKind::IdentifierName;
    }

    return name.kind == SyntaxKind::IdentifierName;
}

MemberSyntax& Parser::parseConstraint(AttrList attributes, std::span<Token> qualifiers,
                                      bool hasBaseClass) {
    bool isStatic = false;
    bool isPure = false;
    for (auto qual : qualifiers) {
        if (qual.kind == TokenKind::StaticKeyword)
            isStatic = true;
        else if (qual.kind == TokenKind::PureKeyword)
            isPure = true;

        if (!isConstraintQualifier(qual.kind)) {
            auto& diag = addDiag(diag::InvalidConstraintQualifier, qual.range());
            diag << qual.rawText();
            break;
        }
    }

    auto keyword = consume();
    auto specifiers = parseClassSpecifierList(true);
    auto& name = parseName();

    bool nameError = false;
    if (!checkConstraintName(name)) {
        nameError = true;
        addDiag(diag::ExpectedConstraintName, keyword.location()) << name.sourceRange();
    }

    if (!specifiers.empty()) {
        // Specifiers are not allowed on static constraints.
        if (isStatic)
            addDiag(diag::StaticFuncSpecifier, specifiers[0]->sourceRange());

        // Final specifier is illegal on pure constraints.
        if (isPure) {
            for (auto specifier : specifiers) {
                if (specifier->keyword.kind == TokenKind::FinalKeyword) {
                    addDiag(diag::FinalWithPure, specifier->sourceRange());
                    break;
                }
            }
        }

        // If there's no base class it can't be marked `extends`.
        if (!hasBaseClass) {
            for (auto specifier : specifiers) {
                if (specifier->keyword.kind == TokenKind::ExtendsKeyword) {
                    auto nameText = name.getLastToken().valueText();
                    if (!nameText.empty())
                        addDiag(diag::OverridingExtends, specifier->sourceRange()) << nameText;
                    break;
                }
            }
        }
    }

    if (peek(TokenKind::OpenBrace)) {
        return factory.constraintDeclaration(attributes, qualifiers, keyword, specifiers, name,
                                             parseConstraintBlock(/* isTopLevel */ true));
    }

    if (!nameError && name.kind != SyntaxKind::IdentifierName)
        addDiag(diag::ExpectedIdentifier, name.sourceRange());

    return factory.constraintPrototype(attributes, qualifiers, keyword, specifiers, name,
                                       expect(TokenKind::Semicolon));
}

ConstraintBlockSyntax& Parser::parseConstraintBlock(bool isTopLevel) {
    Token closeBrace;
    auto openBrace = expect(TokenKind::OpenBrace);
    auto members = parseMemberList<ConstraintItemSyntax>(
        TokenKind::CloseBrace, closeBrace, SyntaxKind::ConstraintBlock,
        [this, isTopLevel](SyntaxKind, bool&) { return parseConstraintItem(false, isTopLevel); });

    return factory.constraintBlock(openBrace, members, closeBrace);
}

ConstraintItemSyntax* Parser::parseConstraintItem(bool allowBlock, bool isTopLevel) {
    switch (peek().kind) {
        case TokenKind::SolveKeyword: {
            auto solve = consume();
            if (!isTopLevel)
                addDiag(diag::SolveBeforeDisallowed, solve.range());

            Token before;
            SmallVector<TokenOrSyntax, 4> beforeBuffer;
            parseList<isPossibleExpressionOrComma, isBeforeOrSemicolon>(
                beforeBuffer, TokenKind::BeforeKeyword, TokenKind::Comma, before,
                RequireItems::True, diag::ExpectedExpression,
                [this] { return &parseExpression(); });

            Token semi;
            SmallVector<TokenOrSyntax, 4> afterBuffer;
            parseList<isPossibleExpressionOrComma, isSemicolon>(
                afterBuffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
                diag::ExpectedExpression, [this] { return &parseExpression(); });

            return &factory.solveBeforeConstraint(solve, beforeBuffer.copy(alloc), before,
                                                  afterBuffer.copy(alloc), semi);
        }
        case TokenKind::DisableKeyword: {
            auto disable = consume();
            auto soft = expect(TokenKind::SoftKeyword);
            auto& name = parseExpression();
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
                elseClause = &factory.elseConstraintClause(elseKeyword,
                                                           *parseConstraintItem(true, false));
            }
            return &factory.conditionalConstraint(ifKeyword, openParen, condition, closeParen,
                                                  constraints, elseClause);
        }
        case TokenKind::UniqueKeyword: {
            auto keyword = consume();
            auto& list = parseRangeList();
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
                if (peek(1).kind == TokenKind::CloseBrace ||
                    !scanTypePart<isNotInConcatenationExpr>(index, TokenKind::OpenBrace,
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
    auto expr =
        &parseSubExpression(ExpressionOptions::ConstraintContext | ExpressionOptions::AllowDist, 0);
    if (peek(TokenKind::MinusArrow)) {
        auto arrow = consume();
        return &factory.implicationConstraint(*expr, arrow, *parseConstraintItem(true, false));
    }

    return &factory.expressionConstraint(Token(), *expr, expect(TokenKind::Semicolon));
}

DistConstraintListSyntax& Parser::parseDistConstraintList() {
    auto dist = consume();

    Token openBrace;
    Token closeBrace;
    std::span<TokenOrSyntax> list;
    parseList<isPossibleValueRangeElement, isEndOfBracedList>(
        TokenKind::OpenBrace, TokenKind::CloseBrace, TokenKind::Comma, openBrace, list, closeBrace,
        RequireItems::True, diag::ExpectedDistItem, [this] { return &parseDistItem(); });

    return factory.distConstraintList(dist, openBrace, list, closeBrace);
}

DistItemBaseSyntax& Parser::parseDistItem() {
    Token defaultKeyword;
    ExpressionSyntax* elem = nullptr;
    if (peek(TokenKind::DefaultKeyword)) {
        defaultKeyword = consume();
        if (parseOptions.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, defaultKeyword.range())
                << toString(parseOptions.languageVersion);
        }
    }
    else {
        elem = &parseValueRangeElement();
    }

    DistWeightSyntax* weight = nullptr;
    if (peek(TokenKind::ColonEquals) || peek(TokenKind::ColonSlash)) {
        auto op = consume();
        weight = &factory.distWeight(op, Token(), parseExpression());
    }
    else if (peek(TokenKind::Colon) &&
             (peek(1).kind == TokenKind::Equals || peek(1).kind == TokenKind::Slash)) {
        // VCS allows the dist weight operators to be split, so allow this with a diagnostic
        // for compat purposes.
        auto op1 = consume();
        auto op2 = consume();
        addDiag(diag::SplitDistWeightOp, op1.range()) << op2.range();
        weight = &factory.distWeight(op1, op2, parseExpression());
    }

    if (elem)
        return factory.distItem(*elem, weight);

    if (!weight ||
        (weight->op.kind != TokenKind::ColonSlash && weight->extraOp.kind != TokenKind::Slash)) {
        auto loc = weight ? weight->op.location()
                          : defaultKeyword.location() + defaultKeyword.rawText().length();
        addDiag(diag::ExpectedToken, loc) << ":/"sv;
    }

    return factory.defaultDistItem(defaultKeyword, weight);
}

std::span<PackageImportDeclarationSyntax*> Parser::parsePackageImports() {
    SmallVector<PackageImportDeclarationSyntax*> buffer;
    while (peek(TokenKind::ImportKeyword))
        buffer.push_back(&parseImportDeclaration({}));
    return buffer.copy(alloc);
}

PackageImportDeclarationSyntax& Parser::parseImportDeclaration(AttrList attributes) {
    auto keyword = consume();

    Token semi;
    SmallVector<TokenOrSyntax, 4> items;
    parseList<isIdentifierOrComma, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                                RequireItems::True, diag::ExpectedPackageImport,
                                                [this] { return &parsePackageImportItem(); });

    auto& result = factory.packageImportDeclaration(attributes, keyword, items.copy(alloc), semi);
    meta.packageImports.push_back(&result);
    return result;
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

MemberSyntax& Parser::parseExportDeclaration(AttrList attributes) {
    auto keyword = consume();

    if (peek(TokenKind::Star)) {
        auto star1 = consume();
        auto doubleColon = expect(TokenKind::DoubleColon);
        auto star2 = expect(TokenKind::Star);
        auto semi = expect(TokenKind::Semicolon);
        return factory.packageExportAllDeclaration(attributes, keyword, star1, doubleColon, star2,
                                                   semi);
    }

    Token semi;
    SmallVector<TokenOrSyntax, 4> items;
    parseList<isIdentifierOrComma, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                                RequireItems::True, diag::ExpectedPackageImport,
                                                [this] { return &parsePackageImportItem(); });

    return factory.packageExportDeclaration(attributes, keyword, items.copy(alloc), semi);
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

    auto& method = parseFunctionPrototype(SyntaxKind::Unknown,
                                          FunctionOptions::AllowEmptyArgNames |
                                              FunctionOptions::AllowImplicitReturn |
                                              FunctionOptions::IsPrototype);

    if (property.kind == TokenKind::PureKeyword && method.keyword.kind == TokenKind::TaskKeyword)
        addDiag(diag::DPIPureTask, method.keyword.range()) << property.range();

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
    if (name != "$fatal"sv && name != "$error"sv && name != "$warning"sv && name != "$info"sv &&
        name != "$static_assert"sv) {
        return nullptr;
    }

    auto nameToken = consume();
    ArgumentListSyntax* argList = nullptr;
    if (peek(TokenKind::OpenParenthesis))
        argList = &parseArgumentList();

    return &factory.elabSystemTask(attributes, nameToken, argList, expect(TokenKind::Semicolon));
}

AssertionItemPortSyntax& Parser::parseAssertionItemPort(SyntaxKind parentKind) {
    auto attributes = parseAttributes();
    auto local = consumeIf(TokenKind::LocalKeyword);

    Token direction;
    if (isPortDirection(peek().kind)) {
        direction = consume();

        bool isSeqOrProp = parentKind == SyntaxKind::SequenceDeclaration ||
                           parentKind == SyntaxKind::PropertyDeclaration;
        if (!local && isSeqOrProp)
            addDiag(diag::AssertionPortDirNoLocal, direction.range());
    }

    if (parentKind == SyntaxKind::LetDeclaration) {
        if (local)
            addDiag(diag::UnexpectedLetPortKeyword, local.range()) << local.valueText();
        else if (direction)
            addDiag(diag::UnexpectedLetPortKeyword, direction.range()) << direction.valueText();
    }
    else if (direction) {
        if (direction.kind == TokenKind::RefKeyword) {
            addDiag(diag::AssertionPortRef, direction.range());
        }
        else if (parentKind == SyntaxKind::PropertyDeclaration &&
                 direction.kind != TokenKind::InputKeyword) {
            addDiag(diag::AssertionPortPropOutput, direction.range());
        }
        else if (parentKind == SyntaxKind::CheckerDeclaration &&
                 direction.kind == TokenKind::InOutKeyword) {
            addDiag(diag::CheckerPortInout, direction.range());
        }
    }

    DataTypeSyntax* type;
    switch (peek().kind) {
        case TokenKind::PropertyKeyword:
            type = &factory.keywordType(SyntaxKind::PropertyType, consume());
            break;
        case TokenKind::SequenceKeyword:
            type = &factory.keywordType(SyntaxKind::SequenceType, consume());
            break;
        case TokenKind::UntypedKeyword:
            type = &factory.keywordType(SyntaxKind::Untyped, consume());
            break;
        default:
            type = &parseDataType(TypeOptions::AllowImplicit);
            break;
    }

    auto name = expect(TokenKind::Identifier);
    auto dimensions = parseDimensionList();

    EqualsAssertionArgClauseSyntax* defaultValue = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        defaultValue = &factory.equalsAssertionArgClause(equals, parsePropertyExpr(0));
    }

    return factory.assertionItemPort(attributes, local, direction, *type, name, dimensions,
                                     defaultValue);
}

AssertionItemPortListSyntax* Parser::parseAssertionItemPortList(SyntaxKind parentKind) {
    if (!peek(TokenKind::OpenParenthesis))
        return nullptr;

    auto openParen = consume();

    SmallVector<TokenOrSyntax, 4> buffer;
    Token closeParen;
    parseList<isPossiblePropertyPortItem, isEndOfParenList>(
        buffer, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::False,
        diag::ExpectedAssertionItemPort,
        [this, parentKind] { return &parseAssertionItemPort(parentKind); });

    return &factory.assertionItemPortList(openParen, buffer.copy(alloc), closeParen);
}

PropertyDeclarationSyntax& Parser::parsePropertyDeclaration(AttrList attributes) {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    auto portList = parseAssertionItemPortList(SyntaxKind::PropertyDeclaration);
    auto semi = expect(TokenKind::Semicolon);

    SmallVector<LocalVariableDeclarationSyntax*> declarations;
    while (isLocalVariableDeclaration())
        declarations.push_back(&parseLocalVariableDeclaration());

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
    auto portList = parseAssertionItemPortList(SyntaxKind::SequenceDeclaration);
    auto semi = expect(TokenKind::Semicolon);

    SmallVector<LocalVariableDeclarationSyntax*> declarations;
    while (isLocalVariableDeclaration())
        declarations.push_back(&parseLocalVariableDeclaration());

    auto& expr = parseSequenceExpr(0, /* isInProperty */ false);
    auto semi2 = expect(TokenKind::Semicolon);
    auto end = expect(TokenKind::EndSequenceKeyword);

    auto blockName = parseNamedBlockClause();
    checkBlockNames(name, blockName);

    return factory.sequenceDeclaration(attributes, keyword, name, portList, semi,
                                       declarations.copy(alloc), expr, semi2, end, blockName);
}

CheckerDeclarationSyntax& Parser::parseCheckerDeclaration(AttrList attributes) {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);
    auto portList = parseAssertionItemPortList(SyntaxKind::CheckerDeclaration);
    auto semi = expect(TokenKind::Semicolon);

    auto savedDefinitionKind = currentDefinitionKind;
    currentDefinitionKind = SyntaxKind::CheckerDeclaration;

    Token end;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndCheckerKeyword, end, SyntaxKind::CheckerDeclaration,
        [this](SyntaxKind parentKind, bool& anyLocalModules) {
            return parseMember(parentKind, anyLocalModules);
        });

    currentDefinitionKind = savedDefinitionKind;

    auto blockName = parseNamedBlockClause();
    checkBlockNames(name, blockName);

    return factory.checkerDeclaration(attributes, keyword, name, portList, semi, members, end,
                                      blockName);
}

Token Parser::parseEdgeKeyword() {
    switch (peek().kind) {
        case TokenKind::EdgeKeyword:
        case TokenKind::PosEdgeKeyword:
        case TokenKind::NegEdgeKeyword:
            return consume();
        default:
            return Token();
    }
}

ClockingSkewSyntax* Parser::parseClockingSkew() {
    Token edge = parseEdgeKeyword();

    TimingControlSyntax* delay = nullptr;
    if (peek(TokenKind::Hash))
        delay = parseTimingControl();

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
    SmallVector<TokenOrSyntax, 4> decls;
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

    if (!blockName)
        blockName = Token::createMissing(alloc, TokenKind::Identifier, peek().location());

    if (!globalOrDefault && blockName.valueText().empty())
        addDiag(diag::ClockingNameEmpty, peek().location());

    Token at = expect(TokenKind::At);

    EventExpressionSyntax* event;
    if (peek(TokenKind::OpenParenthesis)) {
        event = &parseEventExpression();
    }
    else if (peek(TokenKind::SystemIdentifier)) {
        event = &factory.signalEventExpression({}, parsePrimaryExpression(ExpressionOptions::None),
                                               nullptr);
    }
    else {
        event = &factory.signalEventExpression({}, parseName(), nullptr);
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

MemberSyntax& Parser::parseDefaultDisable(AttrList attributes) {
    auto def = expect(TokenKind::DefaultKeyword);
    auto disable = expect(TokenKind::DisableKeyword);
    auto iff = expect(TokenKind::IffKeyword);
    auto& expr = parseExpressionOrDist();
    auto semi = expect(TokenKind::Semicolon);
    return factory.defaultDisableDeclaration(attributes, def, disable, iff, expr, semi);
}

HierarchyInstantiationSyntax& Parser::parseHierarchyInstantiation(AttrList attributes) {
    auto type = expect(TokenKind::Identifier);
    auto parameters = parseParameterValueAssignment();

    // If this is an instantiation of a global module/interface/program,
    // keep track of it in our instantiatedModules set.
    std::string_view name = type.valueText();
    if (!name.empty() && type.kind == TokenKind::Identifier) {
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
    SmallVector<TokenOrSyntax, 8> items;
    parseList<isPossibleInstance, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                               RequireItems::True,
                                               diag::ExpectedHierarchicalInstantiation,
                                               [this] { return &parseHierarchicalInstance(); });

    return factory.hierarchyInstantiation(attributes, type, parameters, items.copy(alloc), semi);
}

PrimitiveInstantiationSyntax& Parser::parsePrimitiveInstantiation(AttrList attributes) {
    Token type;
    if (isGateType(peek().kind))
        type = consume();
    else
        type = expect(TokenKind::Identifier);

    NetStrengthSyntax* strength = nullptr;
    if (peek(TokenKind::OpenParenthesis) && isDriveStrength(peek(1).kind)) {
        if (type.kind == TokenKind::PullUpKeyword || type.kind == TokenKind::PullDownKeyword)
            strength = parsePullStrength(type);
        else {
            strength = parseDriveStrength();
            SLANG_ASSERT(strength);
            switch (type.kind) {
                case TokenKind::CmosKeyword:
                case TokenKind::RcmosKeyword:
                case TokenKind::NmosKeyword:
                case TokenKind::PmosKeyword:
                case TokenKind::RnmosKeyword:
                case TokenKind::RpmosKeyword:
                case TokenKind::TranIf0Keyword:
                case TokenKind::TranIf1Keyword:
                case TokenKind::RtranIf0Keyword:
                case TokenKind::RtranIf1Keyword:
                case TokenKind::TranKeyword:
                case TokenKind::RtranKeyword:
                    addDiag(diag::DriveStrengthNotAllowed, type.range())
                        << type.valueText() << strength->sourceRange();
                    break;
                default:
                    break;
            }
        }
    }

    auto delay = parseDelay3();
    if (delay) {
        switch (type.kind) {
            case TokenKind::PullDownKeyword:
            case TokenKind::PullUpKeyword:
            case TokenKind::TranKeyword:
            case TokenKind::RtranKeyword:
                addDiag(diag::DelaysNotAllowed, delay->sourceRange())
                    << type.valueText() << type.range();
                break;
            case TokenKind::AndKeyword:
            case TokenKind::NandKeyword:
            case TokenKind::OrKeyword:
            case TokenKind::NorKeyword:
            case TokenKind::XorKeyword:
            case TokenKind::XnorKeyword:
            case TokenKind::BufKeyword:
            case TokenKind::NotKeyword:
            case TokenKind::TranIf0Keyword:
            case TokenKind::TranIf1Keyword:
            case TokenKind::RtranIf0Keyword:
            case TokenKind::RtranIf1Keyword:
            case TokenKind::Identifier:
                if (delay->kind == SyntaxKind::Delay3) {
                    if (auto d3 = delay->as<Delay3Syntax>().delay3) {
                        auto range = d3->sourceRange();
                        if (type.kind == TokenKind::Identifier) {
                            addDiag(diag::Delay3UdpNotAllowed, range);
                        }
                        else {
                            addDiag(diag::Delay3NotAllowed, range)
                                << type.valueText() << type.range();
                        }
                    }
                }
                break;
            default:
                break;
        }
    }

    Token semi;
    SmallVector<TokenOrSyntax, 8> items;
    parseList<isPossibleInstance, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                               RequireItems::True,
                                               diag::ExpectedHierarchicalInstantiation,
                                               [this] { return &parseHierarchicalInstance(); });

    return factory.primitiveInstantiation(attributes, type, strength, delay, items.copy(alloc),
                                          semi);
}

CheckerInstantiationSyntax& Parser::parseCheckerInstantiation(AttrList attributes) {
    auto& type = parseName(NameOptions::NoClassScope);
    auto parameters = parseParameterValueAssignment();

    Token semi;
    SmallVector<TokenOrSyntax, 8> items;
    parseList<isPossibleInstance, isSemicolon>(items, TokenKind::Semicolon, TokenKind::Comma, semi,
                                               RequireItems::True,
                                               diag::ExpectedHierarchicalInstantiation,
                                               [this] { return &parseHierarchicalInstance(); });

    return factory.checkerInstantiation(attributes, type, parameters, items.copy(alloc), semi);
}

HierarchicalInstanceSyntax& Parser::parseHierarchicalInstance() {
    InstanceNameSyntax* decl = nullptr;
    if (!peek(TokenKind::OpenParenthesis)) {
        auto name = expect(TokenKind::Identifier);
        auto dimensions = parseDimensionList();
        decl = &factory.instanceName(name, dimensions);
    }

    Token openParen;
    Token closeParen;
    std::span<TokenOrSyntax> items;
    parseList<isPossiblePortConnection, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, items,
        closeParen, RequireItems::False, diag::ExpectedPortConnection,
        [this] { return &parsePortConnection(); }, AllowEmpty::True);

    return factory.hierarchicalInstance(decl, openParen, items, closeParen);
}

BindDirectiveSyntax& Parser::parseBindDirective(AttrList attr) {
    Token keyword = consume();
    auto& target = parseName();

    BindTargetListSyntax* targetInstances = nullptr;
    if (peek(TokenKind::Colon)) {
        if (target.kind != SyntaxKind::IdentifierName)
            addDiag(diag::BindDirectiveInvalidName, target.sourceRange());

        auto colon = consume();

        SmallVector<TokenOrSyntax, 4> names;
        while (true) {
            names.push_back(&parseName());
            if (!peek(TokenKind::Comma))
                break;

            names.push_back(consume());
        }

        targetInstances = &factory.bindTargetList(colon, names.copy(alloc));
    }

    meta.hasBindDirectives = true;

    if (peek(TokenKind::Identifier) && peek(1).kind == TokenKind::DoubleColon &&
        peek(2).kind == TokenKind::Identifier) {
        return factory.bindDirective(attr, keyword, target, targetInstances,
                                     parseCheckerInstantiation({}));
    }
    else {
        return factory.bindDirective(attr, keyword, target, targetInstances,
                                     parseHierarchyInstantiation({}));
    }
}

UdpPortDeclSyntax& Parser::parseUdpPortDecl(bool& isReg) {
    auto attrs = parseAttributes();

    if (peek(TokenKind::OutputKeyword) || peek(TokenKind::RegKeyword)) {
        auto output = consumeIf(TokenKind::OutputKeyword);
        auto reg = consumeIf(TokenKind::RegKeyword);
        auto name = expect(TokenKind::Identifier);

        if (reg)
            isReg = true;

        EqualsValueClauseSyntax* init = nullptr;
        if (output && reg && peek(TokenKind::Equals)) {
            auto equals = consume();
            init = &factory.equalsValueClause(equals, parseExpression());
        }

        return factory.udpOutputPortDecl(attrs, output, reg, name, init);
    }

    auto input = expect(TokenKind::InputKeyword);

    SmallVector<TokenOrSyntax, 4> ports;
    while (true) {
        auto name = expect(TokenKind::Identifier);
        ports.push_back(&factory.identifierName(name));

        if (!peek(TokenKind::Comma) || peek(1).kind != TokenKind::Identifier)
            break;

        ports.push_back(consume());
    }

    return factory.udpInputPortDecl(attrs, input, ports.copy(alloc));
}

UdpPortListSyntax& Parser::parseUdpPortList(bool& isSequential) {
    auto openParen = expect(TokenKind::OpenParenthesis);

    if (peek(TokenKind::Dot) && peek(1).kind == TokenKind::Star) {
        auto dot = consume();
        auto star = consume();
        auto closeParen = expect(TokenKind::CloseParenthesis);
        return factory.wildcardUdpPortList(openParen, dot, star, closeParen,
                                           expect(TokenKind::Semicolon));
    }
    else if (peek(TokenKind::OutputKeyword) || peek(TokenKind::InputKeyword)) {
        Token closeParen;
        SmallVector<TokenOrSyntax, 4> ports;
        parseList<isPossibleUdpPort, isEndOfParenList>(
            ports, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::True,
            diag::ExpectedUdpPort,
            [this, &isSequential] { return &parseUdpPortDecl(isSequential); });

        return factory.ansiUdpPortList(openParen, ports.copy(alloc), closeParen,
                                       expect(TokenKind::Semicolon));
    }
    else {
        Token closeParen;
        SmallVector<TokenOrSyntax, 4> ports;
        parseList<isIdentifierOrComma, isEndOfParenList>(
            ports, TokenKind::CloseParenthesis, TokenKind::Comma, closeParen, RequireItems::True,
            diag::ExpectedUdpPort,
            [this] { return &factory.identifierName(expect(TokenKind::Identifier)); });

        return factory.nonAnsiUdpPortList(openParen, ports.copy(alloc), closeParen,
                                          expect(TokenKind::Semicolon));
    }
}

UdpFieldBaseSyntax* Parser::parseUdpField(bool required, bool isInput, bool isSequential,
                                          bool& sawTransition) {
    auto checkTransition = [&](std::optional<SourceLocation> loc = {}) {
        if (isInput) {
            if (sawTransition) {
                if (!loc)
                    loc = peek().location();
                addDiag(diag::UdpDupTransition, *loc);
            }
            else if (!isSequential) {
                if (!loc)
                    loc = peek().location();
                addDiag(diag::UdpEdgeInComb, *loc);
            }
        }
        sawTransition = true;
    };

    auto nextSymbol = [&](bool required, bool insideTrans, bool& error) {
        switch (peek().kind) {
            case TokenKind::Question:
                return consume();
            case TokenKind::Star:
                if (!insideTrans)
                    checkTransition();
                return consume();
            case TokenKind::Minus: {
                auto tok = consume();
                if (isInput) {
                    error = true;
                    addDiag(diag::UdpInvalidMinus, tok.location());
                }
                return tok;
            }
            case TokenKind::Identifier:
            case TokenKind::IntegerLiteral: {
                auto tok = consume();
                auto text = tok.rawText();
                for (size_t i = 0; i < text.length(); i++) {
                    char c = charToLower(text[i]);
                    switch (c) {
                        case '0':
                        case '1':
                        case 'x':
                        case 'b':
                            break;
                        case 'r':
                        case 'f':
                        case 'p':
                        case 'n':
                            if (!insideTrans)
                                checkTransition(tok.location() + i);
                            break;
                        default:
                            error = true;
                            addDiag(diag::UdpInvalidSymbol, tok.location() + i) << c;
                            break;
                    }
                }
                return tok;
            }
            default:
                if (required) {
                    error = true;
                    addDiag(diag::ExpectedUdpSymbol, peek().location());
                }
                return Token();
        }
    };

    if (peek(TokenKind::OpenParenthesis)) {
        checkTransition();
        auto openParen = consume();

        bool error = false;
        auto first = nextSymbol(true, true, error);
        auto second = nextSymbol(false, true, error);
        auto closeParen = expect(TokenKind::CloseParenthesis);
        auto result = &factory.udpEdgeField(openParen, first, second, closeParen);

        if (!closeParen.isMissing()) {
            if (!isInput) {
                addDiag(diag::UdpInvalidTransition, result->sourceRange());
            }
            else if (!error) {
                if (first.rawText().size() + second.rawText().size() != 2) {
                    addDiag(diag::UdpTransitionLength, result->sourceRange());
                }
                else {
                    char chars[2] = {};
                    int idx = 0;
                    for (auto tok : {first, second}) {
                        auto text = tok.rawText();
                        for (size_t i = 0; i < text.length(); i++) {
                            char c = charToLower(text[i]);
                            switch (c) {
                                case '0':
                                case '1':
                                case 'x':
                                case 'b':
                                case '?':
                                    chars[idx++] = c;
                                    break;
                                default:
                                    addDiag(diag::UdpInvalidEdgeSymbol, tok.location() + i) << c;
                                    break;
                            }
                        }
                    }

                    if (idx == 2 && chars[0] == chars[1] && chars[0] != 'b' && chars[0] != '?')
                        addDiag(diag::UdpTransSameChar, result->sourceRange());
                }
            }
        }

        return result;
    }

    bool error = false;
    auto next = nextSymbol(required, false, error);
    if (!next)
        return nullptr;

    if (!isInput && !error) {
        auto text = next.rawText();
        if (text.length() > 1) {
            addDiag(diag::UdpSingleChar, next.range());
        }
        else if (!text.empty()) {
            char c = charToLower(text[0]);
            switch (c) {
                case '*':
                case 'r':
                case 'f':
                case 'p':
                case 'n':
                    addDiag(diag::UdpInvalidInputOnly, next.location()) << c;
                    break;
                default:
                    break;
            }
        }
    }

    return &factory.udpSimpleField(next);
}

UdpEntrySyntax& Parser::parseUdpEntry(bool isSequential) {
    bool sawTransition = false;
    SmallVector<UdpFieldBaseSyntax*, 4> inputs;
    while (true) {
        auto field = parseUdpField(inputs.empty(), /* isInput */ true, isSequential, sawTransition);
        if (!field)
            break;

        inputs.push_back(field);
    }

    auto colon1 = expect(TokenKind::Colon);
    auto nextState = parseUdpField(!inputs.empty(), /* isInput */ false, isSequential,
                                   sawTransition);

    Token colon2;
    UdpFieldBaseSyntax* currentState = nullptr;
    if (peek(TokenKind::Colon)) {
        colon2 = consume();
        currentState = std::exchange(nextState, parseUdpField(true, /* isInput */ false,
                                                              isSequential, sawTransition));
    }

    auto checkNonInput = [&](const UdpFieldBaseSyntax* syntax, bool isOutput) {
        if (!syntax || syntax->kind != SyntaxKind::UdpSimpleField)
            return;

        auto tok = syntax->as<UdpSimpleFieldSyntax>().field;
        auto raw = tok.rawText();
        if (!raw.empty()) {
            switch (raw[0]) {
                case '?':
                case 'b':
                    if (isOutput)
                        addDiag(diag::UdpInvalidOutput, tok.location()) << raw[0];
                    break;
                case '-':
                    if (!isOutput || !isSequential)
                        addDiag(diag::UdpInvalidMinus, tok.location());
                    break;
                default:
                    break;
            }
        }
    };

    checkNonInput(currentState, false);
    checkNonInput(nextState, true);

    auto semi = expect(TokenKind::Semicolon);

    if (currentState && !isSequential)
        addDiag(diag::UdpCombState, currentState->sourceRange());
    else if (!currentState && isSequential && !semi.isMissing())
        addDiag(diag::UdpSequentialState, semi.location());

    return factory.udpEntry(inputs.copy(alloc), colon1, currentState, colon2, nextState, semi);
}

UdpBodySyntax& Parser::parseUdpBody(bool isSequential) {
    SmallVector<TokenOrSyntax, 4> portDecls;
    while (isPossibleUdpPort(peek().kind)) {
        auto current = peek();
        portDecls.push_back(&parseUdpPortDecl(isSequential));
        portDecls.push_back(expect(TokenKind::Semicolon));

        if (current == peek()) {
            // We didn't consume any tokens, so we're looking at
            // something invalid.
            skipToken({});
        }
    }

    UdpInitialStmtSyntax* initial = nullptr;
    if (peek(TokenKind::InitialKeyword)) {
        auto keyword = consume();
        auto name = expect(TokenKind::Identifier);
        auto equals = expect(TokenKind::Equals);
        auto& expr = parsePrimaryExpression(ExpressionOptions::None);
        auto semi = expect(TokenKind::Semicolon);
        initial = &factory.udpInitialStmt(keyword, name, equals, expr, semi);
    }

    auto table = expect(TokenKind::TableKeyword);

    SmallVector<UdpEntrySyntax*> entries;
    while (isPossibleUdpEntry(peek().kind)) {
        auto current = peek();
        entries.push_back(&parseUdpEntry(isSequential));

        if (current == peek()) {
            // We didn't consume any tokens, so we're looking at
            // something invalid.
            skipToken({});
        }
    }

    auto endtable = expect(TokenKind::EndTableKeyword);
    return factory.udpBody(portDecls.copy(alloc), initial, table, entries.copy(alloc), endtable);
}

UdpDeclarationSyntax& Parser::parseUdpDeclaration(AttrList attr) {
    auto primitive = consume();
    auto name = expect(TokenKind::Identifier);

    bool isSequential = false;
    auto& portList = parseUdpPortList(isSequential);
    auto& body = parseUdpBody(isSequential);
    auto endprim = expect(TokenKind::EndPrimitiveKeyword);

    NamedBlockClauseSyntax* endBlockName = parseNamedBlockClause();
    checkBlockNames(name, endBlockName);

    return factory.udpDeclaration(attr, primitive, name, portList, body, endprim, endBlockName);
}

SpecparamDeclaratorSyntax& Parser::parseSpecparamDeclarator(SyntaxKind parentKind) {
    auto name = expect(TokenKind::Identifier);
    auto equals = expect(TokenKind::Equals);
    auto openParen = consumeIf(TokenKind::OpenParenthesis);
    auto& expr1 = parseMinTypMaxExpression();

    const bool isPathPulse = name.valueText().starts_with("PATHPULSE$"sv);

    Token comma;
    ExpressionSyntax* expr2 = nullptr;
    if (openParen && peek(TokenKind::Comma)) {
        comma = consume();
        expr2 = &parseMinTypMaxExpression();
    }

    Token closeParen;
    if (openParen)
        closeParen = expect(TokenKind::CloseParenthesis);

    if (!name.isMissing()) {
        if (isPathPulse && parentKind != SyntaxKind::SpecifyBlock)
            addDiag(diag::PulseControlSpecifyParent, name.range());

        if (!isPathPulse && expr2) {
            auto last = expr2->getLastToken();
            SourceRange range(expr1.getFirstToken().location(),
                              last.location() + last.rawText().length());
            addDiag(diag::PulseControlPATHPULSE, name.range()) << range;
        }
    }

    return factory.specparamDeclarator(name, equals, openParen, expr1, comma, expr2, closeParen);
}

SpecparamDeclarationSyntax& Parser::parseSpecparam(AttrList attr, SyntaxKind parentKind) {
    auto keyword = consume();

    auto dim = parseDimension();
    SmallVector<VariableDimensionSyntax*> dims;
    if (dim)
        dims.push_back(dim);

    auto& type = factory.implicitType(Token(), dims.copy(alloc), placeholderToken());

    Token semi;
    SmallVector<TokenOrSyntax, 4> buffer;
    parseList<isIdentifierOrComma, isNotIdOrComma>(buffer, TokenKind::Semicolon, TokenKind::Comma,
                                                   semi, RequireItems::True,
                                                   diag::ExpectedDeclarator, [this, parentKind] {
                                                       return &parseSpecparamDeclarator(parentKind);
                                                   });

    return factory.specparamDeclaration(attr, keyword, type, buffer.copy(alloc), semi);
}

std::span<TokenOrSyntax> Parser::parsePathTerminals() {
    SmallVector<TokenOrSyntax, 4> results;
    while (true) {
        results.push_back(&parseName(NameOptions::NoClassScope));
        if (!peek(TokenKind::Comma))
            break;

        results.push_back(consume());
    }

    return results.copy(alloc);
}

PathDeclarationSyntax& Parser::parsePathDeclaration() {
    auto parsePolarity = [&] {
        switch (peek().kind) {
            case TokenKind::Plus:
            case TokenKind::Minus:
                return consume();
            default:
                return Token();
        }
    };

    auto checkTerminals = [&](std::span<TokenOrSyntax> terminals, bool isFull) {
        if (!isFull && terminals.size() > 2) {
            Token first = terminals[2].node()->getFirstToken();
            Token last = terminals.back().node()->getLastToken();
            addDiag(diag::MultipleParallelTerminals,
                    SourceRange{first.location(), last.location() + last.rawText().length()});
        }
    };

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto edge = parseEdgeKeyword();
    auto inputs = parsePathTerminals();
    auto polarity = parsePolarity();

    // In specify blocks, +=> (and -=>) should be parsed as '+' and '=>',
    // but of course the lexer tokenizes it as '+=' and '>' so we need to
    // work around that here.
    Token op;
    bool isFull = false;
    if (!polarity && (peek(TokenKind::PlusEqual) || peek(TokenKind::MinusEqual))) {
        polarity = consume();
        op = consumeIf(TokenKind::GreaterThan);
        if (!op) {
            addDiag(diag::ExpectedPathOp, polarity.location() + 1);
            op = missingToken(TokenKind::GreaterThan, peek().location());
        }
        else if (!op.trivia().empty()) {
            addDiag(diag::ExpectedPathOp, polarity.location() + 1);
        }
    }
    else {
        switch (peek().kind) {
            case TokenKind::StarArrow:
                isFull = true;
                op = consume();
                break;
            case TokenKind::EqualsArrow:
                op = consume();
                break;
            default:
                addDiag(diag::ExpectedPathOp, peek().location());
                op = missingToken(TokenKind::EqualsArrow, peek().location());
                break;
        }
    }

    checkTerminals(inputs, isFull);

    PathSuffixSyntax* suffix;
    if (peek(TokenKind::OpenParenthesis)) {
        auto suffixOpenParen = consume();
        auto outputs = parsePathTerminals();
        auto polarity2 = parsePolarity();

        // The polarity we just tried to parse could have been a '+' or a '-' next
        // to the expected colon, which would get lexed together as a single token.
        // In that case don't bother trying to find another colon token.
        Token colon;
        if (!polarity2 && (peek(TokenKind::PlusColon) || peek(TokenKind::MinusColon)))
            polarity2 = consume();
        else
            colon = expect(TokenKind::Colon);

        auto& expr = parseExpression();
        auto suffixCloseParen = expect(TokenKind::CloseParenthesis);
        suffix = &factory.edgeSensitivePathSuffix(suffixOpenParen, outputs, polarity2, colon, expr,
                                                  suffixCloseParen);

        checkTerminals(outputs, isFull);
    }
    else {
        auto outputs = parsePathTerminals();
        suffix = &factory.simplePathSuffix(outputs);
        checkTerminals(outputs, isFull);
    }

    auto closeParen = expect(TokenKind::CloseParenthesis);
    auto& desc = factory.pathDescription(openParen, edge, inputs, polarity, op, *suffix,
                                         closeParen);

    auto equals = expect(TokenKind::Equals);

    Token semi;
    Token valueOpenParen, valueCloseParen;
    std::span<TokenOrSyntax> delays;

    if (peek(TokenKind::OpenParenthesis)) {
        parseList<isPossibleExpressionOrComma, isEndOfParenList>(
            TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma,
            valueOpenParen, delays, valueCloseParen, RequireItems::True, diag::ExpectedExpression,
            [this] { return &parseMinTypMaxExpression(); });
        semi = expect(TokenKind::Semicolon);
    }
    else {
        SmallVector<TokenOrSyntax, 4> buffer;
        parseList<isPossibleExpressionOrComma, isSemicolon>(
            buffer, TokenKind::Semicolon, TokenKind::Comma, semi, RequireItems::True,
            diag::ExpectedExpression, [this] { return &parseMinTypMaxExpression(); });
        delays = buffer.copy(alloc);
    }

    if (delays.size() > 0 && delays.size() != 1 && delays.size() != 3 && delays.size() != 5 &&
        delays.size() != 11 && delays.size() != 23) {
        auto& lastDelay = delays.back();
        auto range = lastDelay.isNode() ? lastDelay.node()->sourceRange()
                                        : lastDelay.token().range();
        addDiag(diag::WrongSpecifyDelayCount, range);
    }

    return factory.pathDeclaration(nullptr, desc, equals, valueOpenParen, delays, valueCloseParen,
                                   semi);
}

EdgeDescriptorSyntax& Parser::parseEdgeDescriptor() {
    Token t1;
    if (peek(TokenKind::IntegerLiteral) || peek(TokenKind::Identifier)) {
        t1 = consume();
    }
    else {
        addDiag(diag::ExpectedEdgeDescriptor, peek().location());
        t1 = Token::createMissing(alloc, TokenKind::Identifier, peek().location());
        return factory.edgeDescriptor(t1, Token());
    }

    Token t2;
    if (t1.kind == TokenKind::IntegerLiteral && peek(TokenKind::Identifier) &&
        peek().trivia().empty()) {
        t2 = consume();
    }

    auto t1Raw = t1.rawText();
    auto t2Raw = t2.rawText();

    SourceRange range = t1.range();
    if (t2)
        range = {t1.range().start(), t2.range().end()};

    if (t1Raw.length() + t2Raw.length() != 2) {
        addDiag(diag::InvalidEdgeDescriptor, range);
    }
    else {
        char edges[2];
        memcpy(edges, t1Raw.data(), t1Raw.length());
        if (!t2Raw.empty())
            memcpy(edges + t1Raw.length(), t2Raw.data(), t2Raw.length());

        bool bad = false;
        bool bothUnknown = true;
        for (char& edge : edges) {
            char c = edge = charToLower(edge);
            if (c == '0' || c == '1') {
                bothUnknown = false;
            }
            else if (!bad && (c != 'x' && c != 'z')) {
                bad = true;
                addDiag(diag::InvalidEdgeDescriptor, range);
            }
        }

        if (!bad && (edges[0] == edges[1] || bothUnknown)) {
            addDiag(diag::InvalidEdgeDescriptor, range);
        }
    }

    return factory.edgeDescriptor(t1, t2);
}

TimingCheckArgSyntax& Parser::parseTimingCheckArg() {
    if (peek(TokenKind::Comma) || peek(TokenKind::CloseParenthesis))
        return factory.emptyTimingCheckArg(placeholderToken());

    auto parseCondition = [&]() -> TimingCheckEventConditionSyntax* {
        if (!peek(TokenKind::TripleAnd))
            return nullptr;

        // The syntax in the BNF for condition expressions is nonsensical,
        // and there is some discussion in the Mantis tracker about how it's
        // a holdover from Verilog-XL and should likely be replaced with just
        // a plain old expression, so that's what we're doing here.
        auto tripleAnd = consume();
        auto& expr = parseExpression();
        return &factory.timingCheckEventCondition(tripleAnd, expr);
    };

    auto edge = parseEdgeKeyword();
    if (edge) {
        EdgeControlSpecifierSyntax* control = nullptr;
        if (peek(TokenKind::OpenBracket)) {
            Token openBracket, closeBracket;
            std::span<TokenOrSyntax> list;
            parseList<isPossibleEdgeDescriptor, isEndOfBracketedList>(
                TokenKind::OpenBracket, TokenKind::CloseBracket, TokenKind::Comma, openBracket,
                list, closeBracket, RequireItems::True, diag::ExpectedEdgeDescriptor,
                [this] { return &parseEdgeDescriptor(); });

            control = &factory.edgeControlSpecifier(openBracket, list, closeBracket);

            // List is allowed to have up to 6 specifiers (plus 5 commas)
            if (list.size() > 11) {
                auto& lastDesc = list[11];
                auto range = lastDesc.isNode() ? lastDesc.node()->sourceRange()
                                               : lastDesc.token().range();
                addDiag(diag::TooManyEdgeDescriptors, range);
            }

            if (edge.kind != TokenKind::EdgeKeyword) {
                addDiag(diag::EdgeDescWrongKeyword, edge.range())
                    << edge.valueText() << control->sourceRange();
            }
        }

        auto& terminal = parseName();
        auto cond = parseCondition();
        return factory.timingCheckEventArg(edge, control, terminal, cond);
    }

    auto& expr = parseMinTypMaxExpression();
    auto cond = parseCondition();
    if (cond)
        return factory.timingCheckEventArg(Token(), nullptr, expr, cond);

    else
        return factory.expressionTimingCheckArg(expr);
}

SystemTimingCheckSyntax& Parser::parseSystemTimingCheck() {
    auto name = consume();

    Token openParen, closeParen;
    std::span<TokenOrSyntax> list;
    parseList<isPossibleTimingCheckArg, isEndOfParenList>(
        TokenKind::OpenParenthesis, TokenKind::CloseParenthesis, TokenKind::Comma, openParen, list,
        closeParen, RequireItems::True, diag::ExpectedExpression,
        [this] { return &parseTimingCheckArg(); }, AllowEmpty::True);

    return factory.systemTimingCheck(nullptr, name, openParen, list, closeParen,
                                     expect(TokenKind::Semicolon));
}

MemberSyntax* Parser::parseSpecifyItem() {
    switch (peek().kind) {
        case TokenKind::SpecParamKeyword:
            return &parseSpecparam({}, SyntaxKind::SpecifyBlock);
        case TokenKind::PulseStyleOnDetectKeyword:
        case TokenKind::PulseStyleOnEventKeyword:
        case TokenKind::ShowCancelledKeyword:
        case TokenKind::NoShowCancelledKeyword: {
            auto keyword = consume();
            auto names = parsePathTerminals();
            return &factory.pulseStyleDeclaration(nullptr, keyword, names,
                                                  expect(TokenKind::Semicolon));
        }
        case TokenKind::OpenParenthesis:
            return &parsePathDeclaration();
        case TokenKind::IfNoneKeyword: {
            auto keyword = consume();
            auto& path = parsePathDeclaration();
            if (path.desc->suffix->kind == SyntaxKind::EdgeSensitivePathSuffix) {
                addDiag(diag::IfNoneEdgeSensitive, keyword.range())
                    << path.desc->suffix->sourceRange();
            }

            return &factory.ifNonePathDeclaration(nullptr, keyword, path);
        }
        case TokenKind::IfKeyword: {
            auto keyword = consume();
            auto openParen = expect(TokenKind::OpenParenthesis);
            auto& pred = parseExpression();
            auto closeParen = expect(TokenKind::CloseParenthesis);
            auto& path = parsePathDeclaration();
            return &factory.conditionalPathDeclaration(nullptr, keyword, openParen, pred,
                                                       closeParen, path);
        }
        case TokenKind::SystemIdentifier:
            return &parseSystemTimingCheck();
        default:
            // Otherwise, we got nothing and should just return null so that our caller
            // will skip and try again.
            return nullptr;
    }
}

SpecifyBlockSyntax& Parser::parseSpecifyBlock(AttrList attributes) {
    auto specify = consume();

    Token endspecify;
    auto members = parseMemberList<MemberSyntax>(
        TokenKind::EndSpecifyKeyword, endspecify, SyntaxKind::SpecifyBlock,
        [this](SyntaxKind, bool&) { return parseSpecifyItem(); });

    return factory.specifyBlock(attributes, specify, members, endspecify);
}

NetAliasSyntax& Parser::parseNetAlias(AttrList attributes) {
    auto keyword = consume();

    Token semi;
    SmallVector<TokenOrSyntax, 8> buffer;
    parseList<isPossibleExpressionOrEquals, isSemicolon>(
        buffer, TokenKind::Semicolon, TokenKind::Equals, semi, RequireItems::True,
        diag::ExpectedExpression,
        [this] { return &parsePrimaryExpression(ExpressionOptions::None); });

    return factory.netAlias(attributes, keyword, buffer.copy(alloc), semi);
}

MemberSyntax* Parser::parseExternMember(SyntaxKind parentKind, AttrList attributes) {
    uint32_t index = 1;
    if (!scanAttributes(index))
        return nullptr;

    switch (peek(index).kind) {
        case TokenKind::ModuleKeyword:
        case TokenKind::MacromoduleKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::ProgramKeyword: {
            auto keyword = consume();
            auto actualAttrs = parseAttributes();
            auto& header = parseModuleHeader();
            if (header.ports && header.ports->kind == SyntaxKind::WildcardPortList)
                addDiag(diag::ExternWildcardPortList, header.ports->sourceRange());
            return &factory.externModuleDecl(attributes, keyword, actualAttrs, header);
        }
        case TokenKind::PrimitiveKeyword: {
            bool unused;
            auto keyword = consume();
            auto actualAttrs = parseAttributes();
            auto primitive = consume();
            auto name = expect(TokenKind::Identifier);
            auto& portList = parseUdpPortList(unused);
            if (portList.kind == SyntaxKind::WildcardUdpPortList)
                addDiag(diag::ExternWildcardPortList, portList.sourceRange());
            return &factory.externUdpDecl(attributes, keyword, actualAttrs, primitive, name,
                                          portList);
        }
        case TokenKind::ForkJoinKeyword:
        case TokenKind::FunctionKeyword:
        case TokenKind::TaskKeyword: {
            // If there were more attributes here it's invalid,
            // we'll come back around later after tokens are skipped.
            if (index != 1)
                return nullptr;

            auto keyword = consume();
            auto forkJoin = consumeIf(TokenKind::ForkJoinKeyword);
            auto& proto = parseFunctionPrototype(parentKind, FunctionOptions::IsPrototype);
            auto semi = expect(TokenKind::Semicolon);
            return &factory.externInterfaceMethod(attributes, keyword, forkJoin, proto, semi);
        }
        default:
            return nullptr;
    }
}

ConfigCellIdentifierSyntax& Parser::parseConfigCellIdentifier() {
    auto id1 = expect(TokenKind::Identifier);
    if (peek(TokenKind::Dot)) {
        auto dot = consume();
        return factory.configCellIdentifier(id1, dot, expect(TokenKind::Identifier));
    }

    return factory.configCellIdentifier(Token(), Token(), id1);
}

ConfigLiblistSyntax& Parser::parseConfigLiblist() {
    auto liblist = expect(TokenKind::LibListKeyword);

    SmallVector<Token, 4> tokens;
    while (peek(TokenKind::Identifier)) {
        tokens.push_back(consume());
        if (peek(TokenKind::Comma))
            skipToken(diag::NoCommaInList);
    }

    return factory.configLiblist(liblist, tokens.copy(alloc));
}

ConfigUseClauseSyntax& Parser::parseConfigUseClause() {
    auto use = expect(TokenKind::UseKeyword);

    ConfigCellIdentifierSyntax* name = nullptr;
    if (peek(TokenKind::Identifier) || !peek(TokenKind::Hash))
        name = &parseConfigCellIdentifier();

    auto paramAssignments = parseParameterValueAssignment();
    if (paramAssignments && !paramAssignments->parameters.empty() &&
        paramAssignments->parameters[0]->kind == SyntaxKind::OrderedParamAssignment) {
        addDiag(diag::ConfigParamsOrdered, paramAssignments->parameters[0]->sourceRange());
    }

    Token colon, config;
    if (peek(TokenKind::Colon)) {
        colon = consume();
        config = expect(TokenKind::ConfigKeyword);

        if (!name && !config.isMissing())
            addDiag(diag::ConfigMissingName, config.range());
    }

    return factory.configUseClause(use, name, paramAssignments, colon, config);
}

ConfigDeclarationSyntax& Parser::parseConfigDeclaration(AttrList attributes) {
    auto config = consume();
    auto name = expect(TokenKind::Identifier);
    auto semi1 = expect(TokenKind::Semicolon);

    SmallVector<ParameterDeclarationStatementSyntax*> localparams;
    while (peek(TokenKind::LocalParamKeyword)) {
        Token paramSemi;
        auto& paramBase = parseParameterDecl(consume(), &paramSemi);
        localparams.push_back(
            &factory.parameterDeclarationStatement(nullptr, paramBase, paramSemi));

        if (paramBase.kind == SyntaxKind::ParameterDeclaration) {
            for (auto decl : paramBase.as<ParameterDeclarationSyntax>().declarators) {
                if (decl->initializer) {
                    auto expr = decl->initializer->expr;
                    if (expr->kind == SyntaxKind::ParenthesizedExpression)
                        expr = expr->as<ParenthesizedExpressionSyntax>().expression;

                    switch (expr->kind) {
                        case SyntaxKind::NullLiteralExpression:
                        case SyntaxKind::StringLiteralExpression:
                        case SyntaxKind::RealLiteralExpression:
                        case SyntaxKind::TimeLiteralExpression:
                        case SyntaxKind::IntegerLiteralExpression:
                        case SyntaxKind::UnbasedUnsizedLiteralExpression:
                        case SyntaxKind::IntegerVectorExpression:
                            break;
                        default:
                            addDiag(diag::ConfigParamLiteral, expr->sourceRange());
                            break;
                    }
                }
            }
        }
    }

    auto design = expect(TokenKind::DesignKeyword);

    SmallVector<ConfigCellIdentifierSyntax*> topCells;
    while (peek(TokenKind::Identifier)) {
        topCells.push_back(&parseConfigCellIdentifier());
        if (peek(TokenKind::Comma))
            skipToken(diag::NoCommaInList);
    }

    if (topCells.empty())
        addDiag(diag::ExpectedIdentifier, peek().location());

    auto semi2 = expect(TokenKind::Semicolon);

    const ConfigRuleSyntax* defaultRule = nullptr;
    SmallVector<ConfigRuleSyntax*> rules;
    while (true) {
        auto token = peek();
        if (token.kind == TokenKind::DefaultKeyword) {
            if (defaultRule) {
                auto& diag = addDiag(diag::MultipleDefaultRules, token.range());
                diag.addNote(diag::NotePreviousDefinition, defaultRule->sourceRange());
            }

            consume();
            auto& liblist = parseConfigLiblist();
            rules.push_back(
                &factory.defaultConfigRule(token, liblist, expect(TokenKind::Semicolon)));
            defaultRule = rules.back();
        }
        else if (token.kind == TokenKind::CellKeyword) {
            consume();
            auto& cellName = parseConfigCellIdentifier();

            ConfigRuleClauseSyntax* rule;
            if (peek(TokenKind::UseKeyword))
                rule = &parseConfigUseClause();
            else
                rule = &parseConfigLiblist();

            if (!cellName.library.valueText().empty() && rule->kind == SyntaxKind::ConfigLiblist) {
                addDiag(diag::ConfigSpecificCellLiblist, rule->sourceRange())
                    << cellName.library.range();
            }

            rules.push_back(
                &factory.cellConfigRule(token, cellName, *rule, expect(TokenKind::Semicolon)));
        }
        else if (token.kind == TokenKind::InstanceKeyword) {
            consume();
            auto topModule = expect(TokenKind::Identifier);

            SmallVector<ConfigInstanceIdentifierSyntax*> instanceNames;
            while (peek(TokenKind::Dot)) {
                auto dot = consume();
                instanceNames.push_back(
                    &factory.configInstanceIdentifier(dot, expect(TokenKind::Identifier)));
            }

            ConfigRuleClauseSyntax* rule;
            if (peek(TokenKind::UseKeyword))
                rule = &parseConfigUseClause();
            else
                rule = &parseConfigLiblist();

            rules.push_back(&factory.instanceConfigRule(token, topModule, instanceNames.copy(alloc),
                                                        *rule, expect(TokenKind::Semicolon)));
        }
        else {
            break;
        }
    }

    auto endconfig = expect(TokenKind::EndConfigKeyword);
    auto blockName = parseNamedBlockClause();
    checkBlockNames(name, blockName);

    return factory.configDeclaration(attributes, config, name, semi1, localparams.copy(alloc),
                                     design, topCells.copy(alloc), semi2, rules.copy(alloc),
                                     endconfig, blockName);
}

MemberSyntax* Parser::parseLibraryMember() {
    Token token = peek();
    switch (token.kind) {
        case TokenKind::ConfigKeyword:
            return &parseConfigDeclaration({});
        case TokenKind::Semicolon:
            return &factory.emptyMember(nullptr, nullptr, consume());
        case TokenKind::IncludeKeyword: {
            auto keyword = consume();
            auto& path = parseFilePathSpec();
            auto semi = expect(TokenKind::Semicolon);
            return &factory.libraryIncludeStatement(nullptr, keyword, path, semi);
        }
        case TokenKind::LibraryKeyword:
            return &parseLibraryDecl();
        default:
            return nullptr;
    }
}

LibraryDeclarationSyntax& Parser::parseLibraryDecl() {
    auto keyword = consume();
    auto name = expect(TokenKind::Identifier);

    auto parseFilePathList = [&] {
        SmallVector<TokenOrSyntax, 4> buffer;
        while (true) {
            buffer.push_back(&parseFilePathSpec());

            if (!peek(TokenKind::Comma))
                break;

            buffer.push_back(consume());
        }

        return buffer.copy(alloc);
    };

    auto filePaths = parseFilePathList();

    LibraryIncDirClauseSyntax* incDir = nullptr;
    if (peek(TokenKind::Minus) && peek(1).kind == TokenKind::IncDirKeyword) {
        auto minus = consume();
        auto incDirKeyword = consume();
        auto incPaths = parseFilePathList();
        incDir = &factory.libraryIncDirClause(minus, incDirKeyword, incPaths);
    }

    return factory.libraryDeclaration(nullptr, keyword, name, filePaths, incDir,
                                      expect(TokenKind::Semicolon));
}

FilePathSpecSyntax& Parser::parseFilePathSpec() {
    if (peek(TokenKind::StringLiteral)) {
        auto lit = consume();
        auto path = Token(alloc, TokenKind::IncludeFileName, lit.trivia(), lit.rawText(),
                          lit.location());
        return factory.filePathSpec(path);
    }

    auto nextIsValidPathToken = [&] {
        switch (peek().kind) {
            case TokenKind::Minus:
                return peek(1).kind != TokenKind::IncDirKeyword;
            case TokenKind::Comma:
            case TokenKind::Semicolon:
            case TokenKind::EndOfFile:
                return false;
            default:
                return true;
        }
    };

    if (!nextIsValidPathToken())
        return factory.filePathSpec(expect(TokenKind::IncludeFileName));

    SmallVector<char> text;
    text.push_back('"');

    auto first = peek();
    do {
        text.append_range(consume().rawText());
    } while (nextIsValidPathToken() && peek().trivia().empty());

    text.push_back('"');

    auto path = Token(alloc, TokenKind::IncludeFileName, first.trivia(),
                      toStringView(text.copy(alloc)), first.location());
    return factory.filePathSpec(path);
}

SDFTimescaleSyntax* Parser::parseSDFTimescale() {
    if (peek().kind != TokenKind::OpenParenthesis || peek(1).kind != TokenKind::SDFTimescaleKeyword)
        return nullptr;

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(TokenKind::SDFTimescaleKeyword);

    // Timescale number and unit can be parsed as two tokens (RealLiteral and Identifier) for
    // example: "1 ns" and also as one (TimeLiteral) - 1ns.
    static std::set<std::string_view> validTimescaleNumbers{"1", "10", "100", "1.0", "10", "100.0"};
    auto number = peek();
    std::string_view realLitStr = number.valueText();
    if (number.kind == TokenKind::TimeLiteral) {
        auto numberText = number.valueText();
        // Remove 's' suffix
        realLitStr = numberText.substr(0, numberText.length() - 1);
        // Remove remaining alpha suffix if it present
        if (isalpha(realLitStr.back()) != 0)
            realLitStr = numberText.substr(0, numberText.length() - 2);
    }

    if (!validTimescaleNumbers.contains(realLitStr)) {
        addDiag(diag::InvalidSDFTimescaleUnit, number.range());
        return nullptr;
    }
    number = consume();

    if (number.kind != TokenKind::TimeLiteral) {
        static std::set<std::string_view> validTimescaleUnits{"s", "ms", "us", "ns", "ps", "fs"};
        auto unit = peek();
        if (!validTimescaleUnits.contains(unit.valueText())) {
            addDiag(diag::InvalidSDFTimescaleUnit, number.range());
            return nullptr;
        }
        unit = consume();
        return &factory.sDFTimescale(openParen, keyword,
                                     factory.literalExpression(SyntaxKind::RealLiteralExpression,
                                                               number),
                                     unit, expect(TokenKind::CloseParenthesis));
    }

    return &factory.sDFTimescale(
        openParen, keyword, factory.literalExpression(SyntaxKind::TimeLiteralExpression, number),
        Token(), expect(TokenKind::CloseParenthesis));
}

SDFCharMemberSyntax* Parser::parseSDFCharMember(TokenKind keywordKind, bool weak) {
    if (peek().kind != TokenKind::OpenParenthesis || (weak && peek(1).kind != keywordKind))
        return nullptr;

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(keywordKind);

    auto value = peek();
    if (keywordKind == TokenKind::SDFDividerKeyword) {
        if (value.kind != TokenKind::Slash && value.kind != TokenKind::Dot) {
            addDiag(diag::ExpectedSDFDivider, value.range());
            return nullptr;
        }
    }
    else if (value.kind != TokenKind::StringLiteral) {
        addDiag(diag::ExpectedStringLiteral, value.range());
        return nullptr;
    }
    value = consume();

    return &factory.sDFCharMember(openParen, keyword, value, expect(TokenKind::CloseParenthesis));
}

SDFValueSyntax* Parser::parseSDFValue(const std::set<TokenKind>& endKinds, bool withParens,
                                      bool isSign) {
    // Try to parse such value cases (where braces wrap optional tokens and min, typ, max may be
    // signed or unsigned integers or real literals):
    //     - triple [`(`] [min] `:` [typ] `:` [max] [`)`]
    //     - single [`(`] [value] [`)`]
    // Why the `parseMinTypMaxExpression` method is not used is that parsing this type of SDF
    // expression is more difficult due to the fact that all values can be optional.
    std::set<SyntaxKind> expectedExprKinds{SyntaxKind::IntegerLiteralExpression,
                                           SyntaxKind::RealLiteralExpression};
    if (isSign)
        expectedExprKinds.insert(SyntaxKind::UnaryMinusExpression);

    ExpressionSyntax* min = nullptr;
    ExpressionSyntax* typ = nullptr;
    ExpressionSyntax* max = nullptr;
    Token curr;
    if (withParens)
        curr = expect(TokenKind::OpenParenthesis);

    uint32_t colonCount = 0;
    while (true) {
        curr = peek();
        if (endKinds.contains(curr.kind) || colonCount >= 2)
            break;

        if (curr.kind != TokenKind::Colon && curr.kind != TokenKind::DoubleColon) {
            if (min != nullptr) {
                addDiag(diag::InvalidSDFValueSep, curr.range());
                return &factory.sDFValue(min, typ, max);
            }
        }
        else {
            curr = consume();
            colonCount = (curr.kind == TokenKind::Colon) ? colonCount + 1 : colonCount + 2;
        }

        if (endKinds.contains(peek().kind))
            break;

        auto* expr = &parseExpression();
        if (!expectedExprKinds.contains(expr->kind)) {
            addDiag(diag::InvalidSDFValueExpr, expr->sourceRange());
            return &factory.sDFValue(min, typ, max);
        }

        switch (colonCount) {
            case 0:
                min = expr;
                break;
            case 1:
                typ = expr;
                break;
            case 2:
                max = expr;
                break;
            default:
                break;
        }
    }

    // When colonCount is 0 then single scalar or no scalar is emitted instead of triple
    if (colonCount != 0 && colonCount != 2)
        addDiag(diag::InvalidSDFValueExpr, curr.range());

    // Value propagation in case of single value
    if (colonCount == 0 && min)
        max = typ = min;

    if (withParens)
        curr = expect(TokenKind::CloseParenthesis);
    return &factory.sDFValue(min, typ, max);
}

SDFDelayValueSyntax* Parser::parseSDFDelayValue() {
    SmallVector<SDFValueSyntax*, 3> values;
    if (peek().kind != TokenKind::OpenParenthesis)
        return &factory.sDFDelayValue(values.copy(alloc));

    auto lookahead = peek(1);
    if (lookahead.kind == TokenKind::OpenParenthesis) {
        lookahead = expect(TokenKind::OpenParenthesis);
        values.push_back(
            parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
        values.push_back(
            parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
        lookahead = peek();
        if (lookahead.kind != TokenKind::CloseParenthesis)
            values.push_back(parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true,
                                           /*isSign =*/true));
        lookahead = expect(TokenKind::CloseParenthesis);
    }
    else {
        values.push_back(
            parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    }

    return &factory.sDFDelayValue(values.copy(alloc));
}

std::span<SDFDelayValueSyntax*> Parser::parseSDFDelayValueList(bool isRetain) {
    SmallVector<SDFDelayValueSyntax*, 12> delayValues;
    delayValues.push_back(parseSDFDelayValue());

    while (peek().kind == TokenKind::OpenParenthesis)
        delayValues.push_back(parseSDFDelayValue());

    if (isRetain && delayValues.size() > 3)
        addDiag(diag::InvalidSDFDelayValuesList, peek().range()) << 3;
    else if (delayValues.size() > 12)
        addDiag(diag::InvalidSDFDelayValuesList, peek().range()) << 12;
    return delayValues.copy(alloc);
}

SDFValueMemberSyntax* Parser::parseSDFValueMember(TokenKind keywordKind) {
    if (peek().kind != TokenKind::OpenParenthesis || (peek(1).kind != keywordKind))
        return nullptr;

    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();

    auto* value = parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/false,
                                /*isSign =*/true);
    return &factory.sDFValueMember(openParen, keyword, *value, expect(TokenKind::CloseParenthesis));
}

SDFHeaderSyntax& Parser::parseSDFHeader() {
    auto* version = parseSDFCharMember(TokenKind::SDFVersionKeyword, /*weak =*/false);
    auto* design = parseSDFCharMember(TokenKind::SDFDesignKeyword);
    auto* date = parseSDFCharMember(TokenKind::SDFDateKeyword);
    auto* vendor = parseSDFCharMember(TokenKind::SDFVendorKeyword);
    auto* programName = parseSDFCharMember(TokenKind::SDFProgramKeyword);
    auto* programVersion = parseSDFCharMember(TokenKind::SDFProgramVersionKeyword);
    auto* divider = parseSDFCharMember(TokenKind::SDFDividerKeyword);
    SDFValueMemberSyntax* voltage = parseSDFValueMember(TokenKind::SDFVoltageKeyword);
    auto* process = parseSDFCharMember(TokenKind::SDFProcessKeyword);
    SDFValueMemberSyntax* temperature = parseSDFValueMember(TokenKind::SDFTemperatureKeyword);
    SDFTimescaleSyntax* timescale = parseSDFTimescale();
    return factory.sDFHeader(version, design, date, vendor, programName, programVersion, divider,
                             voltage, process, temperature, timescale);
}

SDFNameSyntax* Parser::parseSDFName() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(TokenKind::SDFNameKeyword);
    LiteralExpressionSyntax* name = nullptr;
    if (peek().kind == TokenKind::StringLiteral)
        name = &factory.literalExpression(SyntaxKind::StringLiteralExpression, consume());
    return &factory.sDFName(openParen, keyword, name, expect(TokenKind::CloseParenthesis));
}

SDFPortSpecSyntax* Parser::parseSDFPortSpec() {
    if (peek().kind == TokenKind::OpenParenthesis)
        return parseSDFPortEdge();
    return parseSDFPort();
}

SDFPortSyntax* Parser::parseSDFPort() {
    NameSyntax& name = parseSDFHierIdentifier();
    auto lookahead = peek();
    if (lookahead.kind == TokenKind::OpenBracket) {
        SelectorSyntax* selector = nullptr;
        auto openBracket = consume();
        auto& lhs = factory.literalExpression(SyntaxKind::IntegerLiteralExpression,
                                              expect(TokenKind::IntegerLiteral));
        auto colon = peek();
        if (colon.kind == TokenKind::Colon) {
            colon = consume();
            auto& rhs = factory.literalExpression(SyntaxKind::IntegerLiteralExpression,
                                                  expect(TokenKind::IntegerLiteral));
            selector = &factory.rangeSelect(SyntaxKind::SimpleRangeSelect, lhs, colon, rhs);
        }
        else {
            selector = &factory.bitSelect(lhs);
        }

        auto closeBracket = expect(TokenKind::CloseBracket);
        auto& elemSelect = factory.elementSelect(openBracket, selector, closeBracket);
        return &factory.sDFPort(factory.elementSelectExpression(name, elemSelect));
    }

    return &factory.sDFPort(name);
}

SDFPortEdgeSyntax* Parser::parseSDFPortEdge() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    // posedge and negedge are not specified as keywords in IEEE 1497-2001 SDF standard
    static const std::set<std::string_view> validTokenText{"posedge", "negedge", "01",
                                                           "10",      "0z",      "1z"};
    bool isError = false;
    auto edge = consume();
    switch (edge.kind) {
        case TokenKind::SDFEdgeIdent0Z:
        case TokenKind::SDFEdgeIdent1Z:
            break;
        case TokenKind::IntegerLiteral:
        case TokenKind::Identifier: {
            if (!validTokenText.contains(edge.valueText()))
                isError = true;
            break;
        }
        default:
            isError = true;
            break;
    }

    if (isError)
        addDiag(diag::InvalidSDFPortEdgeIdentifier, edge.range());

    auto* port = parseSDFPort();
    return &factory.sDFPortEdge(openParen, edge, *port, expect(TokenKind::CloseParenthesis));
}

SDFCellInstanceSyntax* Parser::parseSDFCellInstance() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(TokenKind::SDFInstanceKeyword);
    NameSyntax* name = nullptr;
    auto lookahead = peek();
    switch (lookahead.kind) {
        case TokenKind::Star:
            name = &factory.identifierName(consume());
            break;
        case TokenKind::Identifier:
            name = &parseSDFHierIdentifier();
            break;
        default: {
            if (lookahead.kind != TokenKind::CloseParenthesis)
                addDiag(diag::InvalidSDFCellInstanceIdentifier, lookahead.range());

            name = &factory.identifierName(Token());
            break;
        }
    }

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return &factory.sDFCellInstance(openParen, keyword, *name, closeParen);
}

SDFExceptionSyntax* Parser::parseSDFException() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(TokenKind::SDFExceptionKeyword);
    SmallVector<SDFCellInstanceSyntax*> instances;
    while (peek().kind == TokenKind::OpenParenthesis)
        instances.push_back(parseSDFCellInstance());

    if (instances.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "cell instance"sv;
    return &factory.sDFException(openParen, keyword, instances.copy(alloc),
                                 expect(TokenKind::CloseParenthesis));
}

SDFPathPulseSyntax* Parser::parseSDFPathPulse() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SDFPortSyntax* in = nullptr;
    SDFPortSyntax* out = nullptr;
    // Parse input and output port identifiers
    if (peek().kind == TokenKind::Identifier) {
        in = parseSDFPort();
        out = parseSDFPort();
    }

    SmallVector<SDFValueSyntax*, 2> values;
    values.push_back(parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true,
                                   /*isSign =*/false));

    if (peek().kind != TokenKind::CloseParenthesis)
        values.push_back(parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true,
                                       /*isSign =*/false));

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return &factory.sDFPathPulse(openParen, keyword, in, out, values.copy(alloc), closeParen);
}

SDFRetainSyntax* Parser::parseSDFRetain() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto values = parseSDFDelayValueList(/*isRetain =*/true);
    auto closeParen = expect(TokenKind::CloseParenthesis);
    return &factory.sDFRetain(openParen, keyword, values, closeParen);
}

SDFIOPathSyntax* Parser::parseSDFIOPath() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFPortSpecSyntax*, 2> ports;
    ports.push_back(parseSDFPortSpec());
    ports.push_back(parseSDFPort());
    SDFRetainSyntax* retain = nullptr;
    if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFRetainKeyword)
        retain = parseSDFRetain();
    auto values = parseSDFDelayValueList();
    auto closeParen = expect(TokenKind::CloseParenthesis);
    return &factory.sDFIOPath(openParen, keyword, ports.copy(alloc), retain, values, closeParen);
}

SDFCondSyntax* Parser::parseSDFCond() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    LiteralExpressionSyntax* name = nullptr;
    if (peek().kind == TokenKind::StringLiteral)
        name = &factory.literalExpression(SyntaxKind::StringLiteralExpression, consume());
    auto* condition = &parseSubExpression(ExpressionOptions::SDFCondExpr, 0);
    auto* iOPath = parseSDFIOPath();
    return &factory.sDFCond(openParen, keyword, name, *condition, *iOPath,
                            expect(TokenKind::CloseParenthesis));
}

SDFCondElseSyntax* Parser::parseSDFCondElse() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* iOPath = parseSDFIOPath();
    return &factory.sDFCondElse(openParen, keyword, *iOPath, expect(TokenKind::CloseParenthesis));
}

SDFPortDelayDefSyntax* Parser::parseSDFPortDelayDef() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* port = parseSDFPort();
    auto values = parseSDFDelayValueList();
    return &factory.sDFPortDelayDef(openParen, keyword, *port, values,
                                    expect(TokenKind::CloseParenthesis));
}

SDFInterconnectSyntax* Parser::parseSDFInterconnect() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFPortSyntax*, 2> ports;
    ports.push_back(parseSDFPort());
    ports.push_back(parseSDFPort());
    auto values = parseSDFDelayValueList();
    return &factory.sDFInterconnect(openParen, keyword, ports.copy(alloc), values,
                                    expect(TokenKind::CloseParenthesis));
}

SDFNetDelaySyntax* Parser::parseSDFNetDelay() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* net = parseSDFPort();
    auto values = parseSDFDelayValueList();
    return &factory.sDFNetDelay(openParen, keyword, *net, values,
                                expect(TokenKind::CloseParenthesis));
}

SDFDeviceSyntax* Parser::parseSDFDevice() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SDFPortSyntax* port = nullptr;
    if (peek().kind != TokenKind::OpenParenthesis)
        port = parseSDFPort();
    auto values = parseSDFDelayValueList();
    return &factory.sDFDevice(openParen, keyword, port, values,
                              expect(TokenKind::CloseParenthesis));
}

SDFAbsIncDelayTypeSyntax* Parser::parseSDFAbsIncDelayType() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFDelayDefSyntax*, 4> defs;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        switch (peek(1).kind) {
            case TokenKind::SDFIOPathKeyword:
                defs.push_back(parseSDFIOPath());
                break;
            case TokenKind::SDFCondKeyword:
                defs.push_back(parseSDFCond());
                break;
            case TokenKind::SDFCondElseKeyword:
                defs.push_back(parseSDFCondElse());
                break;
            case TokenKind::SDFPortKeyword:
                defs.push_back(parseSDFPortDelayDef());
                break;
            case TokenKind::SDFInterconnectKeyword:
                defs.push_back(parseSDFInterconnect());
                break;
            case TokenKind::SDFNetDelayKeyword:
                defs.push_back(parseSDFNetDelay());
                break;
            case TokenKind::SDFDeviceKeyword:
                defs.push_back(parseSDFDevice());
                break;
            default:
                next = false;
                break;
        }
    }

    if (defs.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "delay definition"sv;
    return &factory.sDFAbsIncDelayType(openParen, keyword, defs.copy(alloc),
                                       expect(TokenKind::CloseParenthesis));
}

std::span<SDFDelayTypeSyntax*> Parser::parseSDFDelayTypes() {
    SmallVector<SDFDelayTypeSyntax*, 4> types;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        auto lookahead = peek(1);
        switch (lookahead.kind) {
            case TokenKind::SDFPathPulseKeyword:
            case TokenKind::SDFPathPulsePercentKeyword:
                types.push_back(parseSDFPathPulse());
                break;
            case TokenKind::SDFAbsoluteKeyword:
            case TokenKind::SDFIncrementKeyword:
                types.push_back(parseSDFAbsIncDelayType());
                break;
            default:
                next = false;
                break;
        }
    }
    return types.copy(alloc);
}

SDFDelaySpecSyntax* Parser::parseSDFDelaySpec() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto types = parseSDFDelayTypes();
    if (types.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "delay type"sv;
    return &factory.sDFDelaySpec(openParen, keyword, types, expect(TokenKind::CloseParenthesis));
}

SDFPathConstraintSyntax* Parser::parseSDFPathConstraint() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SDFNameSyntax* name = nullptr;
    if (peek().kind == TokenKind::OpenParenthesis)
        name = parseSDFName();

    SmallVector<SDFPortSyntax*, 4> ports;
    while (peek().kind == TokenKind::Identifier)
        ports.push_back(parseSDFPort());

    if (ports.size() < 2)
        addDiag(diag::InvalidSDFPathCnsPortNum, peek().range());

    SmallVector<SDFValueSyntax*, 2> values;
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    return &factory.sDFPathConstraint(openParen, keyword, name, ports.copy(alloc),
                                      values.copy(alloc), expect(TokenKind::CloseParenthesis));
}

SDFPeriodConstraintSyntax* Parser::parseSDFPeriodConstraint() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* port = parseSDFPort();
    auto* value = parseSDFValue({TokenKind::OpenParenthesis, TokenKind::CloseParenthesis},
                                /*withParens =*/true,
                                /*isSign =*/false);
    auto* exception = parseSDFException();
    return &factory.sDFPeriodConstraint(openParen, keyword, *port, *value, exception,
                                        expect(TokenKind::CloseParenthesis));
}

SDFConstraintPathSyntax* Parser::parseSDFConstraintPath() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    SmallVector<SDFPortSyntax*, 2> ports;
    ports.push_back(parseSDFPort());
    ports.push_back(parseSDFPort());
    return &factory.sDFConstraintPath(openParen, ports.copy(alloc),
                                      expect(TokenKind::CloseParenthesis));
}

SDFSumDiffConstraintSyntax* Parser::parseSDFSumDiffConstraint(bool isDiff) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFConstraintPathSyntax*, 4> pathes;
    while (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::Identifier &&
           !(isDiff && pathes.size() == 2))
        pathes.push_back(parseSDFConstraintPath());

    if (pathes.size() < 2)
        addDiag(diag::InvalidSDFSumDiffCnsPathesNum, peek().range());

    SmallVector<SDFValueSyntax*, 2> values;
    bool isSign = !isDiff;
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/isSign));
    if (peek().kind != TokenKind::CloseParenthesis)
        values.push_back(
            parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/isSign));
    return &factory.sDFSumDiffConstraint(openParen, keyword, pathes.copy(alloc), values.copy(alloc),
                                         expect(TokenKind::CloseParenthesis));
}

SDFSkewConstraintSyntax* Parser::parseSDFSkewConstraint() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* portSpec = parseSDFPortSpec();
    auto* value = parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true,
                                /*isSign =*/false);
    return &factory.sDFSkewConstraint(openParen, keyword, *portSpec, *value,
                                      expect(TokenKind::CloseParenthesis));
}

SDFTimingEnvConstructSyntax* Parser::parseSDFTimingEnvConstruct(bool isSlack) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SDFPortEdgeSyntax* edge = nullptr;
    if (!isSlack && peek().kind == TokenKind::OpenParenthesis)
        edge = parseSDFPortEdge();
    auto* port = parseSDFPort();
    SmallVector<SDFValueSyntax*, 4> values;
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/true));
    ExpressionSyntax* period = nullptr;
    if (isSlack && peek().kind != TokenKind::CloseParenthesis) {
        period = &parseExpression();
        if (period->kind != SyntaxKind::RealLiteralExpression &&
            period->kind != SyntaxKind::IntegerLiteralExpression)
            addDiag(diag::ExpectedRealLiteralExpression, period->sourceRange());
    }
    return &factory.sDFTimingEnvConstruct(openParen, keyword, edge, *port, values.copy(alloc),
                                          period, expect(TokenKind::CloseParenthesis));
}

SDFEdgeSyntax* Parser::parseSDFEdge() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto edge = peek();
    auto edgeText = edge.valueText();
    if (edgeText != "posedge" && edgeText != "negedge")
        addDiag(diag::InvalidSDFEdgeSpec, edge.range());
    else
        edge = consume();

    static const std::set<SyntaxKind> expectedExprKinds{SyntaxKind::IntegerLiteralExpression,
                                                        SyntaxKind::RealLiteralExpression,
                                                        SyntaxKind::UnaryMinusExpression};
    SmallVector<ExpressionSyntax*, 2> values;
    auto* expr = &parseExpression();
    if (!expectedExprKinds.contains(expr->kind))
        addDiag(diag::InvalidSDFValueExpr, expr->sourceRange());
    values.push_back(expr);

    if (peek().kind != TokenKind::CloseParenthesis) {
        expr = &parseExpression();
        if (!expectedExprKinds.contains(expr->kind))
            addDiag(diag::InvalidSDFValueExpr, expr->sourceRange());
        values.push_back(expr);
    }
    return &factory.sDFEdge(openParen, edge, values.copy(alloc),
                            expect(TokenKind::CloseParenthesis));
}

SDFEdgePairSyntax* Parser::parseSDFEdgePair() {
    SmallVector<SDFEdgeSyntax*, 4> pair;
    pair.push_back(parseSDFEdge());
    pair.push_back(parseSDFEdge());
    if (pair[0]->edge.valueText() == pair[1]->edge.valueText())
        addDiag(diag::InvalidSDFEdgePair, pair[1]->edge.range())
            << ((pair[1]->edge.valueText() == "posedge") ? "negedge"sv : "posedge"sv);
    return &factory.sDFEdgePair(pair.copy(alloc));
}

SDFWaveformSyntax* Parser::parseSDFWaveform() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto* port = parseSDFPort();
    auto* period = &parseExpression();
    if (period->kind != SyntaxKind::RealLiteralExpression &&
        period->kind != SyntaxKind::IntegerLiteralExpression)
        addDiag(diag::ExpectedRealLiteralExpression, period->sourceRange());

    SmallVector<SDFEdgePairSyntax*, 4> edgeList;
    while (peek().kind == TokenKind::OpenParenthesis)
        edgeList.push_back(parseSDFEdgePair());

    if (edgeList.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "edge pair"sv;

    const auto* first = *edgeList.begin();
    for (const auto* pair : edgeList) {
        if (pair == first)
            continue;

        const auto edge = pair->edges[0]->edge;
        if (edge.valueText() != first->edges[0]->edge.valueText())
            addDiag(diag::InvalidSDFEdgePair, edge.range())
                << ((edge.valueText() == "posedge") ? "negedge"sv : "posedge"sv);
    }

    return &factory.sDFWaveform(openParen, keyword, *port, *period, edgeList.copy(alloc),
                                expect(TokenKind::CloseParenthesis));
}

std::span<SDFTimingEnvDefSyntax*> Parser::parseSDFTimingEnvDefs() {
    SmallVector<SDFTimingEnvDefSyntax*, 4> defs;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        auto lookahead = peek(1);
        switch (lookahead.kind) {
            case TokenKind::SDFPathConstraintKeyword:
                defs.push_back(parseSDFPathConstraint());
                break;
            case TokenKind::SDFPeriodConstraintKeyword:
                defs.push_back(parseSDFPeriodConstraint());
                break;
            case TokenKind::SDFSumKeyword:
                defs.push_back(parseSDFSumDiffConstraint());
                break;
            case TokenKind::SDFDiffKeyword:
                defs.push_back(parseSDFSumDiffConstraint(/*isDiff =*/true));
                break;
            case TokenKind::SDFSkewConstraintKeyword:
                defs.push_back(parseSDFSkewConstraint());
                break;
            case TokenKind::SDFArrivalKeyword:
            case TokenKind::SDFDepartureKeyword:
                defs.push_back(parseSDFTimingEnvConstruct());
                break;
            case TokenKind::SDFSlackKeyword:
                defs.push_back(parseSDFTimingEnvConstruct(/*isSlack =*/true));
                break;
            case TokenKind::SDFWaveformKeyword:
                defs.push_back(parseSDFWaveform());
                break;
            default:
                next = false;
                break;
        }
    }
    return defs.copy(alloc);
}

SDFPortTimingCheckSyntax* Parser::parseSDFPortTimingCheck() {
    if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFCondKeyword)
        return parseSDFTimingCheckCondition(TokenKind::SDFCondKeyword);
    return parseSDFPortSpec();
}

SDFTimingCheckConditionSyntax* Parser::parseSDFTimingCheckCondition(TokenKind keywordKind) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = expect(keywordKind);
    LiteralExpressionSyntax* name = nullptr;
    if (peek().kind == TokenKind::StringLiteral)
        name = &factory.literalExpression(SyntaxKind::StringLiteralExpression, consume());
    auto* condition = &parseSubExpression(ExpressionOptions::SDFTimingCheckCondExpr, 0);
    SDFPortSpecSyntax* portSpec = nullptr;
    if (peek().kind != TokenKind::CloseParenthesis)
        portSpec = parseSDFPortSpec();
    return &factory.sDFTimingCheckCondition(openParen, keyword, name, *condition, portSpec,
                                            expect(TokenKind::CloseParenthesis));
}

SDFTimingCheckDefSyntax* Parser::parseSDFTimingCheckDef(bool hasTwoPorts, bool hasTwoValues,
                                                        bool isSign, bool hasConds) {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFPortTimingCheckSyntax*, 2> ports;
    bool hasPortConds = false;
    if (hasConds) {
        if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFCondKeyword)
            hasPortConds = true;
        ports.push_back(parseSDFPortTimingCheck());
        if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFCondKeyword)
            hasPortConds = true;
        ports.push_back(parseSDFPortTimingCheck());
    }
    else {
        ports.push_back(parseSDFPortSpec());
        if (hasTwoPorts)
            ports.push_back(parseSDFPortSpec());
    }

    SmallVector<SDFValueSyntax*, 2> values;
    values.push_back(
        parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true, /*isSign =*/isSign));
    if (hasTwoValues)
        values.push_back(parseSDFValue({TokenKind::CloseParenthesis}, /*withParens =*/true,
                                       /*isSign =*/isSign));
    SmallVector<SDFTimingCheckConditionSyntax*, 2> conditions;
    if (hasConds && !hasPortConds) {
        if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFSCondKeyword)
            conditions.push_back(parseSDFTimingCheckCondition(TokenKind::SDFSCondKeyword));
        if (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFCCondKeyword)
            conditions.push_back(parseSDFTimingCheckCondition(TokenKind::SDFCCondKeyword));
    }
    return &factory.sDFTimingCheckDef(openParen, keyword, ports.copy(alloc), values.copy(alloc),
                                      conditions.copy(alloc), expect(TokenKind::CloseParenthesis));
}

std::span<SDFTimingCheckDefSyntax*> Parser::parseSDFTimingCheckDefs() {
    SmallVector<SDFTimingCheckDefSyntax*, 4> defs;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        auto lookahead = peek(1);
        switch (lookahead.kind) {
            case TokenKind::SDFSetupKeyword:
            case TokenKind::SDFHoldKeyword:
            case TokenKind::SDFRecoveryKeyword:
            case TokenKind::SDFRemovalKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/true,
                                                      /*hasTwoValues =*/false, /*isSign =*/false));
                break;
            case TokenKind::SDFSetupHoldKeyword:
            case TokenKind::SDFRecremKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/true, /*hasTwoValues =*/true,
                                                      /*isSign =*/true, /*hasConds =*/true));
                break;
            case TokenKind::SDFSkewKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/true,
                                                      /*hasTwoValues =*/false, /*isSign =*/true));
                break;
            case TokenKind::SDFBidirectSkewKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/true, /*hasTwoValues =*/true,
                                                      /*isSign =*/false));
                break;
            case TokenKind::SDFWidthKeyword:
            case TokenKind::SDFPeriodKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/false,
                                                      /*hasTwoValues =*/false, /*isSign =*/false));
                break;
            case TokenKind::SDFNochangeKeyword:
                defs.push_back(parseSDFTimingCheckDef(/*hasTwoPorts =*/true, /*hasTwoValues =*/true,
                                                      /*isSign =*/true));
                break;
            default:
                next = false;
                break;
        }
    }
    return defs.copy(alloc);
}

SDFTimingCheckSyntax* Parser::parseSDFTimingCheck() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto defs = parseSDFTimingCheckDefs();
    if (defs.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "timing check definition"sv;
    return &factory.sDFTimingCheck(openParen, keyword, defs, expect(TokenKind::CloseParenthesis));
}

SDFTimingEnvSyntax* Parser::parseSDFTimingEnv() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto defs = parseSDFTimingEnvDefs();
    if (defs.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "timing environment definition"sv;
    return &factory.sDFTimingEnv(openParen, keyword, defs, expect(TokenKind::CloseParenthesis));
}

SDFLabelDefSyntax* Parser::parseSDFLabelDef() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto* identifier = &factory.identifierName(expect(TokenKind::Identifier));
    auto values = parseSDFDelayValueList();
    return &factory.sDFLabelDef(openParen, *identifier, values,
                                expect(TokenKind::CloseParenthesis));
}

SDFLabelTypeSyntax* Parser::parseSDFLabelType() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    SmallVector<SDFLabelDefSyntax*, 4> defs;
    while (peek().kind == TokenKind::OpenParenthesis) {
        defs.push_back(parseSDFLabelDef());
    }

    if (defs.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "label definition"sv;
    return &factory.sDFLabelType(openParen, keyword, defs.copy(alloc),
                                 expect(TokenKind::CloseParenthesis));
}

std::span<SDFLabelTypeSyntax*> Parser::parseSDFLabelTypes() {
    SmallVector<SDFLabelTypeSyntax*, 4> types;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        auto lookahead = peek(1);
        switch (lookahead.kind) {
            case TokenKind::SDFAbsoluteKeyword:
            case TokenKind::SDFIncrementKeyword:
                types.push_back(parseSDFLabelType());
                break;
            default:
                next = false;
                break;
        }
    }
    return types.copy(alloc);
}

SDFLabelSyntax* Parser::parseSDFLabel() {
    auto openParen = expect(TokenKind::OpenParenthesis);
    auto keyword = consume();
    auto types = parseSDFLabelTypes();
    if (types.empty())
        addDiag(diag::ExpectedSDFMember, peek().range()) << "label type"sv;
    return &factory.sDFLabel(openParen, keyword, types, expect(TokenKind::CloseParenthesis));
}

std::span<SDFTimingSpecSyntax*> Parser::parseSDFTimingSpecs() {
    SmallVector<SDFTimingSpecSyntax*, 4> timingSpecs;
    bool next = true;
    while (next && peek().kind == TokenKind::OpenParenthesis) {
        auto lookahead = peek(1);
        switch (lookahead.kind) {
            case TokenKind::SDFDelayKeyword:
                timingSpecs.push_back(parseSDFDelaySpec());
                break;
            case TokenKind::SDFTimingCheckKeyword:
                timingSpecs.push_back(parseSDFTimingCheck());
                break;
            case TokenKind::SDFTimingEnvKeyword:
                timingSpecs.push_back(parseSDFTimingEnv());
                break;
            case TokenKind::SDFLabelKeyword:
                timingSpecs.push_back(parseSDFLabel());
                break;
            default:
                next = false;
                break;
        }
    }
    return timingSpecs.copy(alloc);
}

std::span<SDFCellSyntax*> Parser::parseSDFCells() {
    SmallVector<SDFCellSyntax*, 4> cells;
    while (peek().kind == TokenKind::OpenParenthesis && peek(1).kind == TokenKind::SDFCellKeyword) {
        auto openParen = consume();
        auto keyword = consume();
        auto* type = parseSDFCharMember(TokenKind::SDFCellTypeKeyword, /*weak =*/false);
        auto* instance = parseSDFCellInstance();
        auto timingSpecs = parseSDFTimingSpecs();
        cells.push_back(&factory.sDFCell(openParen, keyword, *type, *instance, timingSpecs,
                                         expect(TokenKind::CloseParenthesis)));
    }
    return cells.copy(alloc);
}

SDFDelayFileSyntax* Parser::parseSDFDelayFile() {
    if (peek().kind == TokenKind::OpenParenthesis &&
        peek(1).kind == TokenKind::SDFDelayFileKeyword) {
        auto openParen = consume();
        auto keyword = consume();
        SDFHeaderSyntax& header = parseSDFHeader();
        auto cells = parseSDFCells();
        if (cells.empty())
            addDiag(diag::ExpectedSDFMember, peek().range()) << "cell"sv;
        return &factory.sDFDelayFile(nullptr, openParen, keyword, header, cells,
                                     expect(TokenKind::CloseParenthesis));
    }
    return nullptr;
}

void Parser::checkMemberAllowed(const SyntaxNode& member, SyntaxKind parentKind) {
    // If this is an empty member with a missing semicolon, it was some kind
    // of error that has already been reported so don't pile on here.
    if (member.kind == SyntaxKind::EmptyMember) {
        if (member.as<EmptyMemberSyntax>().semi.isMissing())
            return;
    }

    auto error = [&](DiagCode code) { addDiag(code, member.sourceRange()); };

    switch (parentKind) {
        case SyntaxKind::CompilationUnit:
            if (!isAllowedInCompilationUnit(member.kind))
                error(diag::NotAllowedInCU);
            return;
        case SyntaxKind::GenerateBlock:
        case SyntaxKind::GenerateRegion:
            if (!isAllowedInGenerate(member.kind)) {
                error(diag::NotAllowedInGenerate);
                return;
            }

            // Items in generate blocks must also be valid as items in
            // their parent definition kinds.
            switch (currentDefinitionKind) {
                case SyntaxKind::ModuleDeclaration:
                case SyntaxKind::InterfaceDeclaration:
                case SyntaxKind::ProgramDeclaration:
                case SyntaxKind::CheckerDeclaration:
                    checkMemberAllowed(member, currentDefinitionKind);
                    break;
                default:
                    break;
            }
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
        case SyntaxKind::AnonymousProgram:
            if (!isAllowedInAnonymousProgram(member.kind))
                error(diag::NotAllowedInAnonymousProgram);
            return;
        case SyntaxKind::PackageDeclaration:
            if (!isAllowedInPackage(member.kind))
                error(diag::NotAllowedInPackage);
            return;
        case SyntaxKind::ClockingItem:
            if (!isAllowedInClocking(member.kind))
                error(diag::NotAllowedInClocking);
            return;
        case SyntaxKind::CheckerDeclaration:
            if (!isAllowedInChecker(member.kind))
                error(diag::NotAllowedInChecker);
            return;

        // Some kinds of parents already restrict the members they will parse
        // so there's no need to check them here.
        case SyntaxKind::ClassDeclaration:
        case SyntaxKind::Coverpoint:
        case SyntaxKind::CoverCross:
        case SyntaxKind::CovergroupDeclaration:
        case SyntaxKind::ConstraintBlock:
        case SyntaxKind::ClockingDeclaration:
        case SyntaxKind::SpecifyBlock:
        case SyntaxKind::LibraryMap:
        case SyntaxKind::SDFUnit:
            return;
        default:
            SLANG_UNREACHABLE;
    }
}

} // namespace slang::parsing
