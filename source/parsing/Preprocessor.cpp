//------------------------------------------------------------------------------
// Preprocessor.cpp
// SystemVerilog preprocessor and directive support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/Preprocessor.h"

#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/String.h"
#include "slang/util/Version.h"

namespace slang::parsing {

using namespace syntax;

using LF = LexerFacts;

Preprocessor::Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc,
                           Diagnostics& diagnostics, const Bag& options_,
                           span<const DefineDirectiveSyntax* const> inheritedMacros) :
    sourceManager(sourceManager),
    alloc(alloc), diagnostics(diagnostics), options(options_.getOrDefault<PreprocessorOptions>()),
    lexerOptions(options_.getOrDefault<LexerOptions>()), numberParser(diagnostics, alloc) {

    keywordVersionStack.push_back(LF::getDefaultKeywordVersion());
    resetAllDirectives();
    undefineAll();

    // Add in any inherited macros that aren't already set in our map.
    for (auto define : inheritedMacros) {
        auto name = define->name.valueText();
        if (!name.empty())
            macros.emplace(name, define);
    }

    // clang-format off
    pragmaProtectHandlers = {
        { "begin", &Preprocessor::handleProtectBegin },
        { "end", &Preprocessor::handleProtectEnd },
        { "begin_protected", &Preprocessor::handleProtectBeginProtected },
        { "end_protected", &Preprocessor::handleProtectEndProtected },
        { "author", &Preprocessor::handleProtectSingleArgIgnore },
        { "author_info", &Preprocessor::handleProtectSingleArgIgnore },
        { "encrypt_agent", &Preprocessor::handleProtectSingleArgIgnore },
        { "encrypt_agent_info", &Preprocessor::handleProtectSingleArgIgnore },
        { "encoding", &Preprocessor::handleProtectEncoding },
        { "data_keyowner", &Preprocessor::handleProtectSingleArgIgnore },
        { "data_method", &Preprocessor::handleProtectSingleArgIgnore },
        { "data_keyname", &Preprocessor::handleProtectSingleArgIgnore },
        { "data_public_key", &Preprocessor::handleProtectKey },
        { "data_decrypt_key", &Preprocessor::handleProtectKey },
        { "data_block", &Preprocessor::handleProtectBlock },
        { "digest_keyowner", &Preprocessor::handleProtectSingleArgIgnore },
        { "digest_key_method", &Preprocessor::handleProtectSingleArgIgnore },
        { "digest_keyname", &Preprocessor::handleProtectSingleArgIgnore },
        { "digest_public_key", &Preprocessor::handleProtectKey },
        { "digest_decrypt_key", &Preprocessor::handleProtectKey },
        { "digest_method", &Preprocessor::handleProtectSingleArgIgnore },
        { "digest_block", &Preprocessor::handleProtectBlock },
        { "key_keyowner", &Preprocessor::handleProtectSingleArgIgnore },
        { "key_method", &Preprocessor::handleProtectSingleArgIgnore },
        { "key_keyname", &Preprocessor::handleProtectSingleArgIgnore },
        { "key_public_key", &Preprocessor::handleProtectKey },
        { "key_block", &Preprocessor::handleProtectBlock },
        { "decrypt_license", &Preprocessor::handleProtectLicense },
        { "runtime_license", &Preprocessor::handleProtectLicense },
        { "comment", &Preprocessor::handleProtectSingleArgIgnore },
        { "reset", &Preprocessor::handleProtectReset },
        { "viewport", &Preprocessor::handleProtectViewport }
    };
    // clang-format on
}

Preprocessor::Preprocessor(const Preprocessor& other) :
    sourceManager(other.sourceManager), alloc(other.alloc), diagnostics(other.diagnostics),
    numberParser(diagnostics, alloc) {

    keywordVersionStack.push_back(LF::getDefaultKeywordVersion());
}

void Preprocessor::pushSource(string_view source, string_view name) {
    auto buffer = sourceManager.assignText(source);
    pushSource(buffer);

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);
}

void Preprocessor::pushSource(SourceBuffer buffer) {
    ASSERT(buffer.id);

    lexerStack.emplace_back(std::make_unique<Lexer>(buffer, alloc, diagnostics, lexerOptions));
}

void Preprocessor::popSource() {
    if (includeDepth)
        includeDepth--;
    lexerStack.pop_back();
}

void Preprocessor::predefine(const std::string& definition, string_view name) {
    Preprocessor pp(*this);
    pp.pushSource("`define " + definition + "\n", name);

    // Consume all of the definition text.
    while (pp.next().kind != TokenKind::EndOfFile) {
        // Nothing to do but keep going.
    }

    // Look for the macro in the temporary preprocessor's macro map.
    // Any macros found that are not the built-in intrinsic macros should
    // be copied over to our own map.
    for (const auto& pair : pp.macros) {
        if (!pair.second.isIntrinsic())
            macros.insert(pair);
    }
}

bool Preprocessor::undefine(string_view name) {
    auto it = macros.find(name);
    if (it != macros.end() && !it->second.isIntrinsic()) {
        macros.erase(it);
        return true;
    }
    return false;
}

void Preprocessor::undefineAll() {
    macros.clear();
    macros["__FILE__"] = MacroIntrinsic::File;
    macros["__LINE__"] = MacroIntrinsic::Line;

#define DEFINE(name, value) createBuiltInMacro(name, value, #value)
    DEFINE("__slang__"sv, 1);
    createBuiltInMacro("__slang_major__"sv, VersionInfo::getMajor());
    createBuiltInMacro("__slang_minor__"sv, VersionInfo::getMinor());

    DEFINE("SV_COV_START"sv, 0);
    DEFINE("SV_COV_STOP"sv, 1);
    DEFINE("SV_COV_RESET"sv, 2);
    DEFINE("SV_COV_CHECK"sv, 3);
    DEFINE("SV_COV_MODULE"sv, 10);
    DEFINE("SV_COV_HIER"sv, 11);
    DEFINE("SV_COV_ASSERTION"sv, 20);
    DEFINE("SV_COV_FSM_STATE"sv, 21);
    DEFINE("SV_COV_STATEMENT"sv, 22);
    DEFINE("SV_COV_TOGGLE"sv, 23);
    DEFINE("SV_COV_OVERFLOW"sv, -2);
    DEFINE("SV_COV_ERROR"sv, -1);
    DEFINE("SV_COV_NOCOV"sv, 0);
    DEFINE("SV_COV_OK"sv, 1);
    DEFINE("SV_COV_PARTIAL"sv, 2);
#undef DEFINE

    for (std::string predef : options.predefines) {
        // Find location of equals sign to indicate start of body.
        // If there is no equals sign, predefine to a value of 1.
        size_t index = predef.find('=');
        if (index != std::string::npos)
            predef[index] = ' ';
        else
            predef += " 1";
        predefine(predef, options.predefineSource);
    }

    for (const std::string& undef : options.undefines)
        undefine(string_view(undef));
}

bool Preprocessor::isDefined(string_view name) {
    return !name.empty() && macros.find(name) != macros.end();
}

void Preprocessor::setKeywordVersion(KeywordVersion version) {
    keywordVersionStack[0] = version;
}

void Preprocessor::resetAllDirectives() {
    activeTimeScale = std::nullopt;
    defaultNetType = TokenKind::WireKeyword;
    unconnectedDrive = TokenKind::Unknown;
    resetProtectState();
}

std::vector<const DefineDirectiveSyntax*> Preprocessor::getDefinedMacros() const {
    std::vector<const DefineDirectiveSyntax*> results;
    for (auto& [name, def] : macros) {
        if (def.syntax)
            results.push_back(def.syntax);
    }

    std::sort(results.begin(), results.end(),
              [](const DefineDirectiveSyntax* a, const DefineDirectiveSyntax* b) {
                  return a->name.valueText() < b->name.valueText();
              });
    return results;
}

Token Preprocessor::next() {
    return consume();
}

Token Preprocessor::nextProcessed() {
    // The core preprocessing routine; this method pulls raw tokens from various text
    // files and converts them into a unified logical stream of sanitized tokens that
    // future stages like a parser can ingest without difficulty.
    //
    // Start off by grabbing the next raw token, either from the current file, an
    // active include file, or an expanded macro.
    auto token = nextRaw();

    // If we're currently within a macro body, return whatever we got right away.
    // If it was a directive it will be deferred until the macro is used.
    if (inMacroBody)
        return token;

    switch (token.kind) {
        // If we found a directive token, process it and pull another. We don't want
        // to return directives to the caller; we handle them ourselves and turn them
        // into trivia.
        case TokenKind::Directive:
        case TokenKind::MacroQuote:
        case TokenKind::MacroEscapedQuote:
        case TokenKind::MacroPaste:
        case TokenKind::LineContinuation:
            return handleDirectives(token);
        default:
            return token;
    }
}

Token Preprocessor::handleDirectives(Token token) {
    // burn through any preprocessor directives we find and convert them to trivia
    SmallVector<Trivia, 8> trivia;
    while (true) {
        lastConsumed = token;
        switch (token.kind) {
            case TokenKind::MacroQuote:
            case TokenKind::MacroEscapedQuote:
            case TokenKind::MacroPaste:
            case TokenKind::LineContinuation: {
                SmallVector<Token> tokens;
                tokens.push_back(token);
                trivia.push_back(Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc)));
                addDiag(diag::MacroOpsOutsideDefinition, token.range());
                break;
            }
            case TokenKind::Directive:
                switch (token.directiveKind()) {
                    case SyntaxKind::IncludeDirective:
                        trivia.push_back(handleIncludeDirective(token));
                        break;
                    case SyntaxKind::ResetAllDirective:
                        trivia.push_back(handleResetAllDirective(token));
                        break;
                    case SyntaxKind::DefineDirective:
                        trivia.push_back(handleDefineDirective(token));
                        break;
                    case SyntaxKind::MacroUsage: {
                        auto [directive, extra] = handleMacroUsage(token);
                        trivia.push_back(directive);
                        if (extra)
                            trivia.push_back(extra);
                        break;
                    }
                    case SyntaxKind::IfDefDirective:
                        trivia.push_back(handleIfDefDirective(token, false));
                        break;
                    case SyntaxKind::IfNDefDirective:
                        trivia.push_back(handleIfDefDirective(token, true));
                        break;
                    case SyntaxKind::ElsIfDirective:
                        trivia.push_back(handleElsIfDirective(token));
                        break;
                    case SyntaxKind::ElseDirective:
                        trivia.push_back(handleElseDirective(token));
                        break;
                    case SyntaxKind::EndIfDirective:
                        trivia.push_back(handleEndIfDirective(token));
                        break;
                    case SyntaxKind::TimeScaleDirective:
                        trivia.push_back(handleTimeScaleDirective(token));
                        break;
                    case SyntaxKind::DefaultNetTypeDirective:
                        trivia.push_back(handleDefaultNetTypeDirective(token));
                        break;
                    case SyntaxKind::LineDirective:
                        trivia.push_back(handleLineDirective(token));
                        break;
                    case SyntaxKind::UndefDirective:
                        trivia.push_back(handleUndefDirective(token));
                        break;
                    case SyntaxKind::UndefineAllDirective:
                        trivia.push_back(handleUndefineAllDirective(token));
                        break;
                    case SyntaxKind::BeginKeywordsDirective:
                        trivia.push_back(handleBeginKeywordsDirective(token));
                        break;
                    case SyntaxKind::EndKeywordsDirective:
                        trivia.push_back(handleEndKeywordsDirective(token));
                        break;
                    case SyntaxKind::PragmaDirective: {
                        auto [directive, skipped] = handlePragmaDirective(token);
                        trivia.push_back(directive);
                        if (skipped)
                            trivia.push_back(skipped);
                        break;
                    }
                    case SyntaxKind::UnconnectedDriveDirective:
                        trivia.push_back(handleUnconnectedDriveDirective(token));
                        break;
                    case SyntaxKind::NoUnconnectedDriveDirective:
                        trivia.push_back(handleNoUnconnectedDriveDirective(token));
                        break;
                    case SyntaxKind::CellDefineDirective:
                    case SyntaxKind::EndCellDefineDirective:
                        // we don't do anything with celldefine directives
                        trivia.push_back(createSimpleDirective(token));
                        break;
                    default:
                        ASSUME_UNREACHABLE;
                }
                break;
            default:
                trivia.append(token.trivia());
                return token.withTrivia(alloc, trivia.copy(alloc));
        }

        token = nextRaw();
    }
}

Token Preprocessor::nextRaw() {
    // it's possible we have a token buffered from looking ahead when handling a directive
    if (currentToken)
        return std::exchange(currentToken, Token());

    // if we just expanded a macro we'll have tokens from that to return
    if (currentMacroToken) {
        auto result = *currentMacroToken;
        currentMacroToken++;
        if (currentMacroToken == expandedTokens.end()) {
            currentMacroToken = nullptr;
            expandedTokens.clear();
        }
        return result;
    }

    // if this assert fires, the user disregarded an EoF and kept calling next()
    ASSERT(!lexerStack.empty());

    // Pull the next token from the active source.
    // This is the common case.
    auto& source = lexerStack.back();
    auto token = source->lex(keywordVersionStack.back());
    if (token.kind != TokenKind::EndOfFile)
        return token;

    // don't return EndOfFile tokens for included files, fall
    // through to loop to merge trivia
    popSource();
    if (lexerStack.empty())
        return token;

    // Rare case: we have an EoF from an include file... we don't want to return
    // that one, but we do want to merge its trivia with whatever comes next.
    SmallVector<Trivia, 8> trivia;
    auto appendTrivia = [&trivia, this](Token token) {
        SourceLocation loc = token.location();
        for (const auto& t : token.trivia())
            trivia.push_back(t.withLocation(alloc, loc));
    };

    appendTrivia(token);

    while (true) {
        auto& nextSource = lexerStack.back();
        token = nextSource->lex(keywordVersionStack.back());
        appendTrivia(token);
        if (token.kind != TokenKind::EndOfFile)
            break;

        popSource();
        if (lexerStack.empty())
            break;
    }

    // finally found a real token to return, so update trivia and get out of here
    return token.withTrivia(alloc, trivia.copy(alloc));
}

Trivia Preprocessor::handleIncludeDirective(Token directive) {
    // A (valid) macro-expanded include filename will be lexed as either
    // a StringLiteral or the token sequence '<' ... '>'
    Token fileName = peek();
    if (!fileName.isOnSameLine()) {
        fileName = expect(TokenKind::IncludeFileName);
    }
    else if (fileName.kind == TokenKind::LessThan) {
        // Piece together all tokens to form a single filename string.
        SmallVector<Token, 8> tokens;
        consume();

        while (true) {
            Token token = peek();
            if (token.kind == TokenKind::EndOfFile || !token.isOnSameLine()) {
                fileName = expect(TokenKind::IncludeFileName);
                if (!tokens.empty()) {
                    SmallVector<Trivia, 4> trivia;
                    trivia.push_back(Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc)));
                    trivia.append(fileName.trivia());
                    fileName = fileName.withTrivia(alloc, trivia.copy(alloc));
                }
                break;
            }

            if (token.kind == TokenKind::GreaterThan) {
                consume();
                SmallVector<char> text;
                text.push_back('<');

                for (Token cur : tokens) {
                    for (Trivia t : cur.trivia())
                        text.append(t.getRawText());
                    text.append(cur.rawText());
                }

                for (Trivia t : token.trivia())
                    text.append(t.getRawText());
                text.push_back('>');

                fileName = Token(alloc, TokenKind::IncludeFileName, fileName.trivia(),
                                 toStringView(text.copy(alloc)), fileName.location());
                break;
            }

            tokens.push_back(consume());
        }
    }
    else if (fileName.kind == TokenKind::StringLiteral) {
        consume();
        fileName = Token(alloc, TokenKind::IncludeFileName, fileName.trivia(), fileName.rawText(),
                         fileName.location());
    }
    else {
        fileName = expect(TokenKind::IncludeFileName);
    }

    // path should be at least three chars: "a" or <a>
    string_view path = fileName.valueText();
    if (path.length() < 3) {
        if (!fileName.isMissing())
            addDiag(diag::ExpectedIncludeFileName, fileName.range());
    }
    else {
        // remove delimiters
        bool isSystem = path[0] == '<';
        path = path.substr(1, path.length() - 2);
        SourceBuffer buffer = sourceManager.readHeader(path, directive.location(), isSystem);
        if (!buffer.id) {
            addDiag(diag::CouldNotOpenIncludeFile, fileName.range());
        }
        else if (includeDepth >= options.maxIncludeDepth) {
            addDiag(diag::ExceededMaxIncludeDepth, fileName.range());
        }
        else if (includeOnceHeaders.find(buffer.data.data()) == includeOnceHeaders.end()) {
            includeDepth++;
            pushSource(buffer);
        }
    }

    auto syntax = alloc.emplace<IncludeDirectiveSyntax>(directive, fileName);
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleResetAllDirective(Token directive) {
    checkOutsideDesignElement(directive);
    resetAllDirectives();
    return createSimpleDirective(directive);
}

Trivia Preprocessor::handleDefineDirective(Token directive) {
    MacroFormalArgumentListSyntax* formalArguments = nullptr;
    bool bad = false;

    // Next token should be the macro name. We allow the name to be
    // a keyword token for compatibility with other tools.
    Token name;
    if (LF::isKeyword(peek().kind))
        name = consume();
    else
        name = expect(TokenKind::Identifier);

    inMacroBody = true;
    if (name.isMissing())
        bad = true;
    else {
        if (LF::getDirectiveKind(name.valueText()) != SyntaxKind::MacroUsage) {
            addDiag(diag::InvalidMacroName, name.range());
            bad = true;
        }

        // Check if this is a function-like macro, which requires an opening paren with no
        // leading space unless the macro name is escaped, in which case we have to allow one space.
        if (peek(TokenKind::OpenParenthesis)) {
            bool isEscaped = !name.rawText().empty() && name.rawText()[0] == '\\';
            auto trivia = peek().trivia();
            if (trivia.empty() ||
                (isEscaped && trivia.size() == 1 && trivia[0].getRawText() == " "sv)) {
                MacroParser parser(*this);
                formalArguments = parser.parseFormalArgumentList();
            }
        }
    }

    // consume all remaining tokens as macro text
    scratchTokenBuffer.clear();
    while (true) {
        // Figure out when to stop consuming macro text. This involves looking for new lines in the
        // trivia of each token as we grab it. If there's a new line without a preceeding line
        // continuation token we know the macro is finished.
        Token t = peek();
        if (t.kind == TokenKind::EndOfFile)
            break;
        if (t.kind == TokenKind::LineContinuation) {
            scratchTokenBuffer.push_back(consume());
            continue;
        }

        bool hasContinuation = false;
        bool done = false;
        auto triviaList = t.trivia();

        for (const Trivia& trivia : triviaList) {
            switch (trivia.kind) {
                case TriviaKind::EndOfLine:
                    if (hasContinuation)
                        hasContinuation = false;
                    else
                        done = true;
                    break;

                case TriviaKind::LineComment:
                    // A line comment can have a trailing line continuation.
                    if (trivia.getRawText().back() == '\\')
                        hasContinuation = true;
                    break;

                case TriviaKind::BlockComment:
                    if (size_t offset = trivia.getRawText().find_first_of("\r\n");
                        offset != std::string_view::npos) {

                        // Getting the location here is annoying; we need to walk
                        // backward from the token's location.
                        size_t diff = trivia.getRawText().length() - offset;
                        for (auto it = triviaList.rbegin(); it != triviaList.rend(); it++) {
                            if (&(*it) == &trivia)
                                break;
                            diff += it->getRawText().length();
                        }

                        SourceLocation loc = t.location() - diff;
                        addDiag(diag::SplitBlockCommentInDirective, loc);
                        done = true;
                    }
                    break;

                default:
                    break;
            }
            if (done)
                break;
        }
        if (done)
            break;

        scratchTokenBuffer.push_back(consume());
    }
    inMacroBody = false;

    auto result = alloc.emplace<DefineDirectiveSyntax>(directive, name, formalArguments,
                                                       scratchTokenBuffer.copy(alloc));

    if (auto it = macros.find(name.valueText()); it != macros.end()) {
        if (it->second.builtIn) {
            addDiag(diag::InvalidMacroName, name.range());
            bad = true;
        }
        else if (!bad && it->second.valid() && !isSameMacro(*result, *it->second.syntax)) {
            auto& diag = addDiag(diag::RedefiningMacro, name.range());
            diag << name.valueText();
            diag.addNote(diag::NotePreviousDefinition, it->second.syntax->name.location());
        }
    }

    if (!bad)
        macros[name.valueText()] = result;
    return Trivia(TriviaKind::Directive, result);
}

std::pair<Trivia, Trivia> Preprocessor::handleMacroUsage(Token directive) {
    // delegate to a nested function to simplify the error handling paths
    inMacroBody = true;
    auto [actualArgs, extraTrivia] = handleTopLevelMacro(directive);
    inMacroBody = false;

    auto syntax = alloc.emplace<MacroUsageSyntax>(directive, actualArgs);
    return std::make_pair(Trivia(TriviaKind::Directive, syntax), extraTrivia);
}

Trivia Preprocessor::handleIfDefDirective(Token directive, bool inverted) {
    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    bool take = false;
    if (branchStack.empty() || branchStack.back().currentActive) {
        // decide whether the branch is taken or skipped
        take = macros.find(name.valueText()) != macros.end();
        if (inverted)
            take = !take;
    }

    branchStack.emplace_back(BranchEntry(take));

    return parseBranchDirective(directive, name, take);
}

Trivia Preprocessor::handleElsIfDirective(Token directive) {
    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    bool take = shouldTakeElseBranch(directive.location(), true, name.valueText());
    return parseBranchDirective(directive, name, take);
}

Trivia Preprocessor::handleElseDirective(Token directive) {
    bool take = shouldTakeElseBranch(directive.location(), false, "");
    return parseBranchDirective(directive, Token(), take);
}

bool Preprocessor::shouldTakeElseBranch(SourceLocation location, bool isElseIf,
                                        string_view macroName) {
    // empty stack is an error
    if (branchStack.empty()) {
        addDiag(diag::UnexpectedConditionalDirective, location);
        return true;
    }

    // if we already had an else for this branch, we can't have any more elseifs
    BranchEntry& branch = branchStack.back();
    if (branch.hasElse) {
        addDiag(diag::UnexpectedConditionalDirective, location);
        return true;
    }

    // if part of this branch has already been taken, we can't take this one
    bool taken = false;
    if (!branch.anyTaken) {
        // only take this branch if we're the only one in the stack, or our parent is active
        if (branchStack.size() == 1 || branchStack[branchStack.size() - 2].currentActive) {
            // if this is an elseif, the macro name needs to be defined
            taken = !isElseIf || macros.find(macroName) != macros.end();
        }
    }

    branch.currentActive = taken;
    branch.anyTaken |= taken;
    branch.hasElse = !isElseIf;
    return taken;
}

Trivia Preprocessor::parseBranchDirective(Token directive, Token condition, bool taken) {
    scratchTokenBuffer.clear();
    if (!taken) {
        // skip over everything until we find another conditional compilation directive
        while (true) {
            auto token = nextRaw();

            // EoF or conditional directive stops the skipping process
            bool done = false;
            if (token.kind == TokenKind::EndOfFile) {
                addDiag(diag::MissingEndIfDirective, directive.range());
                done = true;
            }
            else if (token.kind == TokenKind::Directive) {
                switch (token.directiveKind()) {
                    case SyntaxKind::IfDefDirective:
                    case SyntaxKind::IfNDefDirective:
                    case SyntaxKind::ElsIfDirective:
                    case SyntaxKind::ElseDirective:
                    case SyntaxKind::EndIfDirective:
                        done = true;
                        break;
                    default:
                        break;
                }
            }

            if (done) {
                // put the token back so that we'll look at it next
                currentToken = token;
                break;
            }
            scratchTokenBuffer.push_back(token);
        }
    }

    SyntaxNode* syntax;
    if (condition) {
        syntax = alloc.emplace<ConditionalBranchDirectiveSyntax>(directive.directiveKind(),
                                                                 directive, condition,
                                                                 scratchTokenBuffer.copy(alloc));
    }
    else {
        syntax = alloc.emplace<UnconditionalBranchDirectiveSyntax>(directive.directiveKind(),
                                                                   directive,
                                                                   scratchTokenBuffer.copy(alloc));
    }
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleEndIfDirective(Token directive) {
    // pop the active branch off the stack
    bool taken = true;
    if (branchStack.empty())
        addDiag(diag::UnexpectedConditionalDirective, directive.range());
    else {
        branchStack.pop_back();
        if (!branchStack.empty() && !branchStack.back().currentActive)
            taken = false;
    }
    return parseBranchDirective(directive, Token(), taken);
}

bool Preprocessor::expectTimeScaleSpecifier(Token& token, TimeScaleValue& value) {
    if (peek(TokenKind::IntegerLiteral)) {
        // We wanted to see a time literal here, but for directives we will allow there
        // to be a space between the integer and suffix portions of the time.
        token = consume();

        auto suffix = peek();
        if (suffix.kind != TokenKind::Identifier || !suffix.isOnSameLine()) {
            addDiag(diag::ExpectedTimeLiteral, token.range());
            return false;
        }

        size_t lengthConsumed;
        auto unit = suffixToTimeUnit(suffix.rawText(), lengthConsumed);
        if (!unit || lengthConsumed != suffix.rawText().length()) {
            addDiag(diag::ExpectedTimeLiteral, token.range());
            return false;
        }

        // Glue the tokens together to form a "time literal"
        consume();
        auto start = token.rawText().data();
        auto end = suffix.rawText().data() + suffix.rawText().size();
        auto text = string_view(start, size_t(end - start));

        token = Token(alloc, TokenKind::TimeLiteral, token.trivia(), text, token.location(),
                      token.intValue().toDouble(), false, unit);
    }
    else {
        token = expect(TokenKind::TimeLiteral);
        if (token.isMissing())
            return false;
    }

    auto checked = TimeScaleValue::fromLiteral(token.realValue(), token.numericFlags().unit());
    if (!checked) {
        addDiag(diag::InvalidTimeScaleSpecifier, token.range());
        return false;
    }

    value = *checked;
    return true;
}

Trivia Preprocessor::handleTimeScaleDirective(Token directive) {
    Token unitToken, precisionToken;
    TimeScaleValue unit, precision;
    bool success = expectTimeScaleSpecifier(unitToken, unit);

    auto slash = expect(TokenKind::Slash);
    success |= expectTimeScaleSpecifier(precisionToken, precision);

    if (success) {
        // Precision must be equal to or smaller than the unit (i.e. more precise).
        if (precision > unit) {
            auto& diag = addDiag(diag::InvalidTimeScalePrecision, precisionToken.range());
            diag << unitToken.range();
        }
        else {
            activeTimeScale = {unit, precision};
        }
    }

    auto timeScale = alloc.emplace<TimeScaleDirectiveSyntax>(directive, unitToken, slash,
                                                             precisionToken);
    return Trivia(TriviaKind::Directive, timeScale);
}

Trivia Preprocessor::handleLineDirective(Token directive) {
    Token lineNumber = expect(TokenKind::IntegerLiteral);
    Token fileName = expect(TokenKind::StringLiteral);
    Token level = expect(TokenKind::IntegerLiteral);

    auto result = alloc.emplace<LineDirectiveSyntax>(directive, lineNumber, fileName, level);

    if (!lineNumber.isMissing() && !fileName.isMissing() && !level.isMissing()) {
        auto levNum = level.intValue().as<uint8_t>();
        auto lineNum = lineNumber.intValue().as<size_t>();

        if (!levNum.has_value() || (*levNum != 0 && *levNum != 1 && *levNum != 2)) {
            // We don't actually use the level for anything, but the spec allows
            // only the values 0,1,2
            addDiag(diag::InvalidLineDirectiveLevel, level.range());
        }
        else if (lineNum) {
            // We should only notify the source manager about the line directive if it
            // is well formed, to avoid very strange line number issues.
            sourceManager.addLineDirective(directive.location(), *lineNum, fileName.valueText(),
                                           *levNum);
        }
    }
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleDefaultNetTypeDirective(Token directive) {
    checkOutsideDesignElement(directive);

    Token netType;
    switch (peek().kind) {
        case TokenKind::WireKeyword:
        case TokenKind::UWireKeyword:
        case TokenKind::WAndKeyword:
        case TokenKind::WOrKeyword:
        case TokenKind::TriKeyword:
        case TokenKind::Tri0Keyword:
        case TokenKind::Tri1Keyword:
        case TokenKind::TriAndKeyword:
        case TokenKind::TriOrKeyword:
        case TokenKind::TriRegKeyword:
            netType = consume();
            defaultNetType = netType.kind;
            break;
        case TokenKind::Identifier:
            // none isn't a keyword but it's special here
            if (peek().rawText() == "none") {
                netType = consume();
                defaultNetType = TokenKind::Unknown;
            }
            break;
        default:
            break;
    }

    if (!netType) {
        addDiag(diag::ExpectedNetType, peek().location());
        netType = Token::createMissing(alloc, TokenKind::WireKeyword, peek().location());
    }

    auto result = alloc.emplace<DefaultNetTypeDirectiveSyntax>(directive, netType);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleUndefDirective(Token directive) {
    Token nameToken = expect(TokenKind::Identifier);

    if (!nameToken.isMissing()) {
        string_view name = nameToken.valueText();
        auto it = macros.find(name);
        if (it != macros.end()) {
            if (!it->second.builtIn)
                macros.erase(it);
            else
                addDiag(diag::UndefineBuiltinDirective, nameToken.range());
        }
    }

    auto result = alloc.emplace<UndefDirectiveSyntax>(directive, nameToken);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleUndefineAllDirective(Token directive) {
    undefineAll();
    return createSimpleDirective(directive);
}

Trivia Preprocessor::handleBeginKeywordsDirective(Token directive) {
    checkOutsideDesignElement(directive);

    Token versionToken = expect(TokenKind::StringLiteral);
    if (!versionToken.isMissing()) {
        auto versionOpt = LF::getKeywordVersion(versionToken.valueText());
        if (!versionOpt)
            addDiag(diag::UnrecognizedKeywordVersion, versionToken.range());
        else
            keywordVersionStack.push_back(*versionOpt);
    }

    auto result = alloc.emplace<BeginKeywordsDirectiveSyntax>(directive, versionToken);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleEndKeywordsDirective(Token directive) {
    checkOutsideDesignElement(directive);

    if (keywordVersionStack.size() == 1)
        addDiag(diag::MismatchedEndKeywordsDirective, directive.range());
    else
        keywordVersionStack.pop_back();

    return createSimpleDirective(directive);
}

std::pair<Trivia, Trivia> Preprocessor::handlePragmaDirective(Token directive) {
    if (peek().kind != TokenKind::Identifier || !peek().isOnSameLine()) {
        addDiag(diag::ExpectedPragmaName, directive.location());
        return {createSimpleDirective(directive), Trivia()};
    }

    SmallVector<TokenOrSyntax, 4> args;
    SmallVector<Token, 4> skipped;
    Token name = consume();
    bool wantComma = false;
    bool ok = true;

    // This loop needs to be careful not to prematurely peek() and pull a
    // new token from the lexer, since some pragmas may change how we lex
    // tokens on the following line (such as pragma protect encoded blocks).
    while (peekSameLine()) {
        if (wantComma) {
            args.push_back(expect(TokenKind::Comma));
            wantComma = false;
        }
        else {
            auto [expr, succeeded] = parsePragmaExpression();
            args.push_back(expr);
            wantComma = true;

            if (!succeeded) {
                while (peekSameLine())
                    skipped.push_back(consume());

                ok = false;
                break;
            }
        }
    }

    auto result = alloc.emplace<PragmaDirectiveSyntax>(directive, name, args.copy(alloc));
    if (ok)
        applyPragma(*result, skipped);

    Trivia skippedTrivia;
    if (!skipped.empty())
        skippedTrivia = Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc));

    return {Trivia(TriviaKind::Directive, result), skippedTrivia};
}

Trivia Preprocessor::handleUnconnectedDriveDirective(Token directive) {
    checkOutsideDesignElement(directive);

    Token strength;
    switch (peek().kind) {
        case TokenKind::Pull0Keyword:
        case TokenKind::Pull1Keyword:
            strength = consume();
            unconnectedDrive = strength.kind;
            break;
        default:
            break;
    }

    if (!strength) {
        addDiag(diag::ExpectedDriveStrength, peek().location());
        strength = Token::createMissing(alloc, TokenKind::Pull0Keyword, peek().location());
    }

    auto result = alloc.emplace<UnconnectedDriveDirectiveSyntax>(directive, strength);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleNoUnconnectedDriveDirective(Token directive) {
    checkOutsideDesignElement(directive);
    unconnectedDrive = TokenKind::Unknown;
    return createSimpleDirective(directive);
}

Trivia Preprocessor::createSimpleDirective(Token directive) {
    auto syntax = alloc.emplace<SimpleDirectiveSyntax>(directive.directiveKind(), directive);
    return Trivia(TriviaKind::Directive, syntax);
}

void Preprocessor::checkOutsideDesignElement(Token directive) {
    if (designElementDepth)
        addDiag(diag::DirectiveInsideDesignElement, directive.range());
}

Token Preprocessor::peek() {
    if (!currentToken)
        currentToken = nextProcessed();
    return currentToken;
}

Token Preprocessor::consume() {
    auto result = peek();
    lastConsumed = currentToken;
    currentToken = Token();
    return result;
}

Token Preprocessor::expect(TokenKind kind) {
    auto result = peek();
    if (result.kind != kind)
        return Token::createExpected(alloc, diagnostics, result, kind, lastConsumed, Token());

    lastConsumed = currentToken;
    currentToken = Token();
    return result;
}

bool Preprocessor::peekSameLine() const {
    if (currentToken)
        return currentToken.isOnSameLine();

    if (currentMacroToken)
        return currentMacroToken->isOnSameLine();

    return lexerStack.back()->isNextTokenOnSameLine();
}

Diagnostic& Preprocessor::addDiag(DiagCode code, SourceLocation location) {
    return diagnostics.add(code, location);
}

Diagnostic& Preprocessor::addDiag(DiagCode code, SourceRange range) {
    return diagnostics.add(code, range);
}

} // namespace slang::parsing
