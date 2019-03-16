//------------------------------------------------------------------------------
// Preprocessor.cpp
// SystemVerilog preprocessor and directive support.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/parsing/Preprocessor.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"

namespace {

using namespace slang;

bool checkTimeMagnitude(double value, string_view& text, TimescaleMagnitude& magnitude) {
    if (value == 1) {
        text = "1";
        magnitude = TimescaleMagnitude::One;
    }
    else if (value == 10) {
        text = "10";
        magnitude = TimescaleMagnitude::Ten;
    }
    else if (value == 100) {
        text = "100";
        magnitude = TimescaleMagnitude::Hundred;
    }
    else {
        return false;
    }
    return true;
}

bool isOnSameLine(Token token) {
    for (auto& t : token.trivia()) {
        switch (t.kind) {
            case TriviaKind::LineComment:
            case TriviaKind::EndOfLine:
            case TriviaKind::SkippedSyntax:
            case TriviaKind::SkippedTokens:
            case TriviaKind::DisabledText:
                return false;
            case TriviaKind::Directive:
                if (t.syntax()->kind != SyntaxKind::MacroUsage)
                    return false;
                break;
            case TriviaKind::BlockComment:
                if (size_t offset = t.getRawText().find_first_of("\r\n");
                    offset != std::string_view::npos) {
                    return false;
                }
                break;
            default:
                break;
        }
    }
    return true;
}

} // namespace

namespace slang {

SyntaxKind getDirectiveKind(string_view directive);

Preprocessor::Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc,
                           Diagnostics& diagnostics, const Bag& options_) :
    sourceManager(sourceManager),
    alloc(alloc), diagnostics(diagnostics), options(options_.getOrDefault<PreprocessorOptions>()),
    lexerOptions(options_.getOrDefault<LexerOptions>()) {
    keywordVersionStack.push_back(getDefaultKeywordVersion());
    resetAllDirectives();
    undefineAll();

    for (std::string& predef : options.predefines) {
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

void Preprocessor::pushSource(string_view source, string_view name) {
    auto buffer = sourceManager.assignText(name, source);
    pushSource(buffer);
}

void Preprocessor::pushSource(SourceBuffer buffer) {
    ASSERT(lexerStack.size() < options.maxIncludeDepth);
    ASSERT(buffer.id);

    auto lexer = alloc.emplace<Lexer>(buffer, alloc, diagnostics, lexerOptions);
    lexerStack.push_back(lexer);
}

void Preprocessor::predefine(string_view definition, string_view fileName) {
    std::string text = "`define " + std::string(definition) + "\n";

    Preprocessor pp(sourceManager, alloc, diagnostics);
    pp.pushSource(sourceManager.assignText(fileName, string_view(text)));
    pp.undefineAll();

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
}

bool Preprocessor::isDefined(string_view name) {
    return !name.empty() && macros.find(name) != macros.end();
}

void Preprocessor::setKeywordVersion(KeywordVersion version) {
    keywordVersionStack[0] = version;
}

void Preprocessor::resetAllDirectives() {
    activeTimescale = std::nullopt;
    defaultNetType = TokenKind::WireKeyword;
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
    SmallVectorSized<Trivia, 16> trivia;
    while (true) {
        lastConsumed = token;
        switch (token.kind) {
            case TokenKind::MacroQuote:
            case TokenKind::MacroEscapedQuote:
            case TokenKind::MacroPaste:
            case TokenKind::LineContinuation: {
                SmallVectorSized<Token, 2> tokens;
                tokens.append(token);
                trivia.append(Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc)));
                addDiag(DiagCode::MacroOpsOutsideDefinition, token.location());
                break;
            }
            case TokenKind::Directive:
                switch (token.directiveKind()) {
                    case SyntaxKind::IncludeDirective:
                        trivia.append(handleIncludeDirective(token));
                        break;
                    case SyntaxKind::ResetAllDirective:
                        trivia.append(handleResetAllDirective(token));
                        break;
                    case SyntaxKind::DefineDirective:
                        trivia.append(handleDefineDirective(token));
                        break;
                    case SyntaxKind::MacroUsage:
                        trivia.append(handleMacroUsage(token));
                        break;
                    case SyntaxKind::IfDefDirective:
                        trivia.append(handleIfDefDirective(token, false));
                        break;
                    case SyntaxKind::IfNDefDirective:
                        trivia.append(handleIfDefDirective(token, true));
                        break;
                    case SyntaxKind::ElsIfDirective:
                        trivia.append(handleElsIfDirective(token));
                        break;
                    case SyntaxKind::ElseDirective:
                        trivia.append(handleElseDirective(token));
                        break;
                    case SyntaxKind::EndIfDirective:
                        trivia.append(handleEndIfDirective(token));
                        break;
                    case SyntaxKind::TimescaleDirective:
                        trivia.append(handleTimescaleDirective(token));
                        break;
                    case SyntaxKind::DefaultNetTypeDirective:
                        trivia.append(handleDefaultNetTypeDirective(token));
                        break;
                    case SyntaxKind::LineDirective:
                        trivia.append(handleLineDirective(token));
                        break;
                    case SyntaxKind::UndefDirective:
                        trivia.append(handleUndefDirective(token));
                        break;
                    case SyntaxKind::UndefineAllDirective:
                        trivia.append(handleUndefineAllDirective(token));
                        break;
                    case SyntaxKind::BeginKeywordsDirective:
                        trivia.append(handleBeginKeywordsDirective(token));
                        break;
                    case SyntaxKind::EndKeywordsDirective:
                        trivia.append(handleEndKeywordsDirective(token));
                        break;
                    case SyntaxKind::PragmaDirective:           // TODO, support pragmas
                    case SyntaxKind::UnconnectedDriveDirective: // Nothing to do for the rest of
                                                                // these
                    case SyntaxKind::NoUnconnectedDriveDirective:
                    case SyntaxKind::CellDefineDirective:
                    case SyntaxKind::EndCellDefineDirective:
                    default:
                        // TODO:
                        // default can be reached in certain error cases
                        trivia.append(createSimpleDirective(token));
                        break;
                }
                break;
            default:
                trivia.appendRange(token.trivia());
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
    lexerStack.pop_back();
    if (lexerStack.empty())
        return token;

    // Rare case: we have an EoF from an include file... we don't want to return
    // that one, but we do want to merge its trivia with whatever comes next.
    SmallVectorSized<Trivia, 16> trivia;
    auto appendTrivia = [&trivia, this](Token token) {
        SourceLocation loc = token.location();
        for (const auto& t : token.trivia())
            trivia.append(t.withLocation(alloc, loc));
    };

    appendTrivia(token);

    while (true) {
        auto& nextSource = lexerStack.back();
        token = nextSource->lex(keywordVersionStack.back());
        appendTrivia(token);
        if (token.kind != TokenKind::EndOfFile)
            break;

        lexerStack.pop_back();
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
    if (!isOnSameLine(fileName)) {
        fileName = expect(TokenKind::IncludeFileName);
    }
    else if (fileName.kind == TokenKind::LessThan) {
        // Piece together all tokens to form a single filename string.
        SmallVectorSized<Token, 8> tokens;
        consume();

        while (true) {
            Token token = peek();
            if (token.kind == TokenKind::EndOfFile || !isOnSameLine(token)) {
                fileName = expect(TokenKind::IncludeFileName);
                if (!tokens.empty()) {
                    SmallVectorSized<Trivia, 4> trivia;
                    trivia.append(Trivia(TriviaKind::SkippedTokens, tokens.copy(alloc)));
                    trivia.appendRange(fileName.trivia());
                    fileName = fileName.withTrivia(alloc, trivia.copy(alloc));
                }
                break;
            }

            if (token.kind == TokenKind::GreaterThan) {
                consume();
                SmallVectorSized<char, 64> text;
                text.append('<');

                for (Token cur : tokens) {
                    for (Trivia t : cur.trivia())
                        text.appendRange(t.getRawText());
                    text.appendRange(cur.rawText());
                }

                for (Trivia t : token.trivia())
                    text.appendRange(t.getRawText());
                text.append('>');

                string_view raw = to_string_view(text.copy(alloc));
                auto info = alloc.emplace<Token::Info>(fileName.trivia(), raw, fileName.location());
                fileName = Token(TokenKind::IncludeFileName, info);
                break;
            }

            tokens.append(consume());
        }
    }
    else if (fileName.kind == TokenKind::StringLiteral) {
        consume();
        fileName = Token(TokenKind::IncludeFileName, fileName.getInfo());
    }
    else {
        fileName = expect(TokenKind::IncludeFileName);
    }

    // path should be at least three chars: "a" or <a>
    string_view path = fileName.valueText();
    if (path.length() < 3) {
        if (!fileName.isMissing())
            addDiag(DiagCode::ExpectedIncludeFileName, fileName.location());
    }
    else {
        // remove delimiters
        bool isSystem = path[0] == '<';
        path = path.substr(1, path.length() - 2);
        SourceBuffer buffer = sourceManager.readHeader(path, directive.location(), isSystem);
        if (!buffer.id)
            addDiag(DiagCode::CouldNotOpenIncludeFile, fileName.location());
        else if (lexerStack.size() >= options.maxIncludeDepth)
            addDiag(DiagCode::ExceededMaxIncludeDepth, fileName.location());
        else
            pushSource(buffer);
    }

    auto syntax = alloc.emplace<IncludeDirectiveSyntax>(directive, fileName);
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleResetAllDirective(Token directive) {
    resetAllDirectives();
    return createSimpleDirective(directive);
}

Trivia Preprocessor::handleDefineDirective(Token directive) {
    MacroFormalArgumentListSyntax* formalArguments = nullptr;
    bool noErrors = false;

    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    inMacroBody = true;

    if (!name.isMissing()) {
        if (getDirectiveKind(name.valueText()) != SyntaxKind::MacroUsage)
            addDiag(DiagCode::InvalidMacroName, name.location());
        else {
            // check if this is a function-like macro, which requires an opening paren with no
            // leading space
            if (peek(TokenKind::OpenParenthesis) && peek().trivia().empty()) {
                MacroParser parser(*this);
                formalArguments = parser.parseFormalArgumentList();
            }
            noErrors = true;
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
            scratchTokenBuffer.append(consume());
            continue;
        }

        bool hasContinuation = false;
        bool done = false;
        for (const Trivia& trivia : t.trivia()) {
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

                        SourceLocation loc; // TODO: set location!
                        addDiag(DiagCode::SplitBlockCommentInDirective, loc);
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

        scratchTokenBuffer.append(consume());
    }
    inMacroBody = false;

    auto result = alloc.emplace<DefineDirectiveSyntax>(directive, name, formalArguments,
                                                       scratchTokenBuffer.copy(alloc));

    if (noErrors)
        macros[name.valueText()] = result;
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleMacroUsage(Token directive) {
    // delegate to a nested function to simplify the error handling paths
    inMacroBody = true;
    auto actualArgs = handleTopLevelMacro(directive);
    inMacroBody = false;

    auto syntax = alloc.emplace<MacroUsageSyntax>(directive, actualArgs);
    return Trivia(TriviaKind::Directive, syntax);
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
        addDiag(DiagCode::UnexpectedConditionalDirective, location);
        return true;
    }

    // if we already had an else for this branch, we can't have any more elseifs
    BranchEntry& branch = branchStack.back();
    if (branch.hasElse) {
        addDiag(DiagCode::UnexpectedConditionalDirective, location);
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
            if (token.kind == TokenKind::EndOfFile)
                done = true;
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
            scratchTokenBuffer.append(token);
        }
    }

    SyntaxNode* syntax;
    if (condition) {
        syntax = alloc.emplace<ConditionalBranchDirectiveSyntax>(
            directive.directiveKind(), directive, condition, scratchTokenBuffer.copy(alloc));
    }
    else {
        syntax = alloc.emplace<UnconditionalBranchDirectiveSyntax>(
            directive.directiveKind(), directive, scratchTokenBuffer.copy(alloc));
    }
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleEndIfDirective(Token directive) {
    // pop the active branch off the stack
    bool taken = true;
    if (branchStack.empty())
        addDiag(DiagCode::UnexpectedConditionalDirective, directive.location());
    else {
        branchStack.pop_back();
        if (!branchStack.empty() && !branchStack.back().currentActive)
            taken = false;
    }
    return parseBranchDirective(directive, Token(), taken);
}

bool Preprocessor::expectTimescaleSpecifier(Token& token, TimescaleValue& value) {
    if (peek(TokenKind::IntegerLiteral)) {
        // We wanted to see a time literal here, but for directives we will allow there
        // to be a space between the integer and suffix portions of the time.
        token = consume();

        TimeUnit unit;
        auto suffix = peek();
        if (suffix.kind != TokenKind::Identifier || !isOnSameLine(suffix) ||
            !suffixToTimeUnit(suffix.rawText(), unit)) {

            addDiag(DiagCode::ExpectedTimeLiteral, token.location());
            return false;
        }

        // Glue the tokens together to form a "time literal"
        consume();
        auto start = token.rawText().data();
        auto text = string_view(start, suffix.rawText().data() + suffix.rawText().size() - start);
        auto info = alloc.emplace<Token::Info>(token.trivia(), text, token.location());
        info->setReal(token.intValue().toDouble(), false);
        info->setTimeUnit(unit);

        token = Token(TokenKind::TimeLiteral, info);
    }
    else {
        token = expect(TokenKind::TimeLiteral);
        if (token.isMissing())
            return false;
    }

    auto checked = TimescaleValue::fromLiteral(token.realValue(), token.numericFlags().unit());
    if (!checked) {
        addDiag(DiagCode::InvalidTimescaleSpecifier, token.location());
        return false;
    }

    value = *checked;
    return true;
}

Trivia Preprocessor::handleTimescaleDirective(Token directive) {
    Token unitToken, precisionToken;
    TimescaleValue unit, precision;
    bool success = expectTimescaleSpecifier(unitToken, unit);

    auto slash = expect(TokenKind::Slash);
    success |= expectTimescaleSpecifier(precisionToken, precision);

    if (success) {
        // Precision must be equal to or smaller than the unit (i.e. more precise).
        if (precision > unit) {
            auto& diag = addDiag(DiagCode::InvalidTimescalePrecision, precisionToken.location());
            diag << unitToken.range() << precisionToken.range();
        }
        else {
            activeTimescale = { unit, precision };
        }
    }

    auto timescale =
        alloc.emplace<TimescaleDirectiveSyntax>(directive, unitToken, slash, precisionToken);
    return Trivia(TriviaKind::Directive, timescale);
}

Trivia Preprocessor::handleLineDirective(Token directive) {
    Token lineNumber = expect(TokenKind::IntegerLiteral);
    Token fileName = expect(TokenKind::StringLiteral);
    Token level = expect(TokenKind::IntegerLiteral);

    auto result = alloc.emplace<LineDirectiveSyntax>(directive, lineNumber, fileName, level);

    if (!lineNumber.isMissing() && !fileName.isMissing() && !level.isMissing()) {
        optional<uint8_t> levNum = level.intValue().as<uint8_t>();
        optional<uint32_t> lineNum = lineNumber.intValue().as<uint32_t>();

        if (!levNum || (levNum != 0 && levNum != 1 && levNum != 2)) {
            // We don't actually use the level for anything, but the spec allows
            // only the values 0,1,2
            addDiag(DiagCode::InvalidLineDirectiveLevel, level.location());
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
        addDiag(DiagCode::ExpectedNetType, peek().location());
        netType = Token::createMissing(alloc, TokenKind::WireKeyword, peek().location());
    }

    auto result = alloc.emplace<DefaultNetTypeDirectiveSyntax>(directive, netType);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleUndefDirective(Token directive) {
    Token nameToken = expect(TokenKind::Identifier);

    // TODO: additional checks for undefining other builtin directives
    if (!nameToken.isMissing()) {
        string_view name = nameToken.valueText();
        auto it = macros.find(name);
        if (it != macros.end()) {
            if (name != "__LINE__" && name != "__FILE__")
                macros.erase(it);
            else
                addDiag(DiagCode::UndefineBuiltinDirective, nameToken.location());
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
    Token versionToken = expect(TokenKind::StringLiteral);
    if (!versionToken.isMissing()) {
        auto versionOpt = getKeywordVersion(versionToken.valueText());
        if (!versionOpt)
            addDiag(DiagCode::UnrecognizedKeywordVersion, versionToken.location());
        else
            keywordVersionStack.push_back(*versionOpt);
    }

    auto result = alloc.emplace<BeginKeywordsDirectiveSyntax>(directive, versionToken);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleEndKeywordsDirective(Token directive) {
    if (keywordVersionStack.size() == 1)
        addDiag(DiagCode::MismatchedEndKeywordsDirective, directive.location());
    else
        keywordVersionStack.pop_back();

    return createSimpleDirective(directive);
}

Trivia Preprocessor::createSimpleDirective(Token directive) {
    auto syntax = alloc.emplace<SimpleDirectiveSyntax>(directive.directiveKind(), directive);
    return Trivia(TriviaKind::Directive, syntax);
}

Preprocessor::MacroDef Preprocessor::findMacro(Token directive) {
    string_view name = directive.valueText().substr(1);
    if (!name.empty() && name[0] == '\\')
        name = name.substr(1);

    auto it = macros.find(name);
    if (it == macros.end())
        return nullptr;
    return it->second;
}

MacroActualArgumentListSyntax* Preprocessor::handleTopLevelMacro(Token directive) {
    auto macro = findMacro(directive);
    if (!macro.valid()) {
        addDiag(DiagCode::UnknownDirective, directive.location()) << directive.valueText();

        // If we see a parenthesis next, let's assume they tried to invoke a function-like macro
        // and skip over the tokens.
        if (peek(TokenKind::OpenParenthesis))
            return MacroParser(*this).parseActualArgumentList();
        return nullptr;
    }

    // if this assert fires, we failed to fully expand nested macros at a previous point
    ASSERT(!currentMacroToken);

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (macro.needsArgs()) {
        actualArgs = MacroParser(*this).parseActualArgumentList();
        if (!actualArgs)
            return nullptr;
    }

    // Expand out the macro
    SmallVectorSized<Token, 32> buffer;
    MacroExpansion expansion{ alloc, buffer, directive, true };
    if (!expandMacro(macro, expansion, actualArgs))
        return actualArgs;

    // The macro is now expanded out into tokens, but some of those tokens might
    // be more macros that need to be expanded, or special characters that
    // perform stringification or concatenation of tokens. It's possible that
    // after concatentation is performed we will have formed new valid macro
    // names that need to be expanded, which is why we loop here.
    SmallSet<DefineDirectiveSyntax*, 8> alreadyExpanded;
    if (!macro.isIntrinsic())
        alreadyExpanded.insert(macro.syntax);

    span<Token const> tokens = buffer.copy(alloc);
    while (true) {
        // Start by recursively expanding out all valid macro usages.
        if (!expandReplacementList(tokens, alreadyExpanded))
            return actualArgs;

        // Now that all macros have been expanded, handle token concatenation and stringification.
        expandedTokens.clear();
        if (!applyMacroOps(tokens, expandedTokens))
            break;

        tokens = expandedTokens;
    }

    // if the macro expanded into any tokens at all, set the pointer
    // so that we'll pull from them next
    if (!expandedTokens.empty())
        currentMacroToken = expandedTokens.begin();

    return actualArgs;
}

bool Preprocessor::applyMacroOps(span<Token const> tokens, SmallVector<Token>& dest) {
    SmallVectorSized<Trivia, 16> emptyArgTrivia;
    SmallVectorSized<Token, 16> stringifyBuffer;
    Token stringify;
    bool anyNewMacros = false;

    // TODO: audit trivia usage here, use of dest.back(), etc

    for (uint32_t i = 0; i < tokens.size(); i++) {
        Token newToken;

        // Once we see a `" token, we start collecting tokens into their own
        // buffer for stringification. Otherwise, just add them to the final
        // expansion buffer.
        Token token = tokens[i];
        switch (token.kind) {
            case TokenKind::MacroQuote:
                if (!stringify) {
                    stringify = token;
                    stringifyBuffer.clear();
                }
                else {
                    // all done stringifying; convert saved tokens to string
                    newToken = Lexer::stringify(alloc, stringify.location(), stringify.trivia(),
                                                stringifyBuffer.begin(), stringifyBuffer.end());
                    stringify = Token();
                }
                break;
            case TokenKind::MacroPaste:
                // Paste together previous token and next token; a macro paste on either end
                // of the buffer or one that borders whitespace should be ignored.
                // This isn't specified in the standard so I'm just guessing.
                if (i == 0 || i == tokens.size() - 1 || !token.trivia().empty() ||
                    !tokens[i + 1].trivia().empty()) {

                    addDiag(DiagCode::IgnoredMacroPaste, token.location());
                }
                else if (stringify) {
                    // if this is right after the opening quote or right before the closing quote,
                    // we're trying to concatenate something with nothing, so assume an error
                    if (stringifyBuffer.empty() || tokens[i + 1].kind == TokenKind::MacroQuote)
                        addDiag(DiagCode::IgnoredMacroPaste, token.location());
                    else {
                        newToken =
                            Lexer::concatenateTokens(alloc, stringifyBuffer.back(), tokens[i + 1]);
                        if (newToken) {
                            stringifyBuffer.pop();
                            ++i;
                        }
                    }
                }
                else {
                    newToken = Lexer::concatenateTokens(alloc, dest.back(), tokens[i + 1]);
                    if (newToken) {
                        dest.pop();
                        ++i;

                        anyNewMacros |= newToken.kind == TokenKind::Directive &&
                                        newToken.directiveKind() == SyntaxKind::MacroUsage;
                    }
                }
                break;
            default:
                newToken = token;
                break;
        }

        if (!newToken)
            continue;

        // If we have an empty macro argument just collect its trivia and use it on the next token
        // we find.
        // TODO: what about trailing trivia that's left over?
        if (newToken.kind == TokenKind::EmptyMacroArgument) {
            emptyArgTrivia.appendRange(newToken.trivia());
            continue;
        }

        if (!emptyArgTrivia.empty()) {
            emptyArgTrivia.appendRange(newToken.trivia());
            newToken = newToken.withTrivia(alloc, emptyArgTrivia.copy(alloc));
            emptyArgTrivia.clear();
        }

        if (!stringify) {
            dest.append(newToken);
            continue;
        }

        // If this is an escaped identifier that includes a `" within it, we need to split the
        // token up to match the behavior of other simulators.
        if (newToken.kind == TokenKind::Identifier &&
            newToken.identifierType() == IdentifierType::Escaped) {

            size_t offset = newToken.rawText().find("`\"");
            if (offset != std::string_view::npos) {
                // Split the token, finish the stringification.
                auto splitInfo = alloc.emplace<Token::Info>(*newToken.getInfo());
                splitInfo->rawText = splitInfo->rawText.substr(0, offset);
                stringifyBuffer.append(Token(TokenKind::Identifier, splitInfo));

                dest.append(Lexer::stringify(alloc, stringify.location(), stringify.trivia(),
                                             stringifyBuffer.begin(), stringifyBuffer.end()));
                stringify = Token();

                // Now we have the unfortunate task of re-lexing the remaining stuff after the split
                // and then appending those tokens to the destination as well.
                SmallVectorSized<Token, 8> splits;
                Lexer::splitTokens(alloc, diagnostics, sourceManager, newToken, offset + 2,
                                   getCurrentKeywordVersion(), splits);
                anyNewMacros |= applyMacroOps(splits, dest);
                continue;
            }
        }

        // TODO: error if no closing quote
        stringifyBuffer.append(newToken);
    }

    return anyNewMacros;
}

bool Preprocessor::expandMacro(MacroDef macro, MacroExpansion& expansion,
                               MacroActualArgumentListSyntax* actualArgs) {
    if (macro.isIntrinsic()) {
        // for now, no intrisics can have arguments
        ASSERT(!actualArgs);
        return expandIntrinsic(macro.intrinsic, expansion);
    }

    DefineDirectiveSyntax* directive = macro.syntax;
    ASSERT(directive);

    // ignore empty macro
    const auto& body = directive->body;
    if (body.empty())
        return true;

    string_view macroName = directive->name.valueText();

    if (!directive->formalArguments) {
        // each macro expansion gets its own location entry
        SourceLocation start = body[0].location();
        SourceLocation expansionLoc = sourceManager.createExpansionLoc(
            start, expansion.getRange().start(), expansion.getRange().end(), macroName);

        // simple macro; just take body tokens
        for (auto token : body)
            expansion.append(token, expansionLoc + (token.location() - start));

        return true;
    }

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = directive->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.size() > formalList.size()) {
        addDiag(DiagCode::TooManyActualMacroArgs, actualArgs->getFirstToken().location());
        return false;
    }

    struct ArgTokens : public span<const Token> {
        using span<const Token>::span;
        using span<const Token>::operator=;
        bool isExpanded = false;
    };
    SmallMap<string_view, ArgTokens, 8> argumentMap;

    for (uint32_t i = 0; i < formalList.size(); i++) {
        auto formal = formalList[i];
        auto name = formal->name.valueText();
        if (name.empty())
            continue;

        const TokenList* tokenList = nullptr;
        if (actualList.size() > i) {
            // if our actual argument is empty and we have a default, take that
            tokenList = &actualList[i]->tokens;
            if (tokenList->empty() && formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
        }
        else {
            // if we've run out of actual args make sure we have a default for this one
            if (formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
            else {
                addDiag(DiagCode::NotEnoughMacroArgs, actualArgs->closeParen.location());
                return false;
            }
        }

        argumentMap.emplace(name, ArgTokens(*tokenList));
    }

    Token endOfArgs = actualArgs->getLastToken();
    SourceLocation start = body[0].location();
    SourceLocation expansionLoc = sourceManager.createExpansionLoc(
        start, expansion.getRange().start(), endOfArgs.location() + endOfArgs.rawText().length(),
        macroName);

    // now add each body token, substituting arguments as necessary
    for (auto& token : body) {
        SourceLocation location = expansionLoc + (token.location() - start);

        if (token.kind != TokenKind::Identifier && !isKeyword(token.kind) &&
            (token.kind != TokenKind::Directive ||
             token.directiveKind() != SyntaxKind::MacroUsage)) {

            expansion.append(token, location);
            continue;
        }

        // Other tools allow arguments to replace matching directive names, e.g.:
        // `define FOO(bar) `bar
        // `define ONE 1
        // `FOO(ONE)   // expands to 1
        string_view text = token.valueText();
        if (token.kind == TokenKind::Directive && text.length() >= 1)
            text = text.substr(1);

        // check for formal param
        auto it = argumentMap.find(text);
        if (it == argumentMap.end()) {
            expansion.append(token, location);
            continue;
        }

        // Fully expand out arguments before substitution to make sure we can detect whether
        // a usage of a macro in a replacement list is valid or an illegal recursion.
        if (!it->second.isExpanded) {
            span<const Token> argTokens = it->second;
            SmallSet<DefineDirectiveSyntax*, 8> alreadyExpanded;
            if (!expandReplacementList(argTokens, alreadyExpanded))
                return false;

            it->second = argTokens;
            it->second.isExpanded = true;
        }

        auto begin = it->second.begin();
        auto end = it->second.end();
        if (begin == end) {
            // The macro argument contained no tokens. We still need to supply an empty token
            // here to ensure that the trivia of the formal parameter is passed on.
            Token empty{ TokenKind::EmptyMacroArgument,
                         alloc.emplace<Token::Info>(token.trivia(), "", token.location()) };
            expansion.append(empty, location);
            continue;
        }

        // We need to ensure that we get correct spacing for the leading token here;
        // it needs to come from the *formal* parameter used in the macro body, not
        // from the argument itself.
        Token first = begin->withTrivia(alloc, token.trivia());
        SourceLocation firstLoc = first.location();

        // Arguments need their own expansion location created; the original
        // location comes from the source file itself, and the expansion location
        // points into the macro body where the formal argument was used.
        SourceLocation argLoc = sourceManager.createExpansionLoc(
            firstLoc, location, location + token.rawText().length(), true);

        // See note above about weird macro usage being argument replaced.
        // In that case we want to fabricate the correct directive token here.
        if (token.kind == TokenKind::Directive) {
            Token grave{ TokenKind::Directive,
                         alloc.emplace<Token::Info>(first.trivia(), "`", first.location()) };
            first = Lexer::concatenateTokens(alloc, grave, first);
        }

        expansion.append(first, argLoc);

        for (++begin; begin != end; begin++) {
            // If this token is in the same buffer as the previous one we can keep using the
            // same expansion location; otherwise we need to create a new one that points into
            // the new buffer as its original location.
            if (begin->location().buffer() != firstLoc.buffer()) {
                firstLoc = begin->location();
                argLoc = sourceManager.createExpansionLoc(
                    firstLoc, location, location + token.rawText().length(), true);
            }
            expansion.append(*begin, argLoc + (begin->location() - firstLoc));
        }
    }

    return true;
}

SourceRange Preprocessor::MacroExpansion::getRange() const {
    return { usageSite.location(), usageSite.location() + usageSite.rawText().length() };
}

void Preprocessor::MacroExpansion::append(Token token, SourceLocation location) {
    if (!any) {
        if (!isTopLevel)
            token = token.withTrivia(alloc, usageSite.trivia());
        else
            token = token.withTrivia(alloc, {});
        any = true;
    }

    // Line continuations gets stripped out when we expand macros and become newline trivia instead.
    if (token.kind == TokenKind::LineContinuation) {
        SmallVectorSized<Trivia, 8> newTrivia;
        newTrivia.appendRange(token.trivia());
        newTrivia.append(Trivia(TriviaKind::EndOfLine, token.rawText().substr(1)));

        auto info = alloc.emplace<Token::Info>(newTrivia.copy(alloc), "", location);
        dest.append(Token(TokenKind::EmptyMacroArgument, info));
    }
    else {
        dest.append(token.withLocation(alloc, location));
    }
}

bool Preprocessor::expandReplacementList(span<Token const>& tokens,
                                         SmallSet<DefineDirectiveSyntax*, 8>& alreadyExpanded) {
    // keep expanding macros in the replacement list until we've got them all
    // use two alternating buffers to hold the tokens
    SmallVectorSized<Token, 64> buffer1;
    SmallVectorSized<Token, 64> buffer2;

    SmallVector<Token>* currentBuffer = &buffer1;
    SmallVector<Token>* nextBuffer = &buffer2;

    bool expandedSomething;
    do {
        expandedSomething = false;
        MacroParser parser(*this);
        parser.setBuffer(tokens);

        // Each round we will fully expand all macros that we come across. We use the
        // `alreadyExpanded` set to avoid recursively expanding macros infinitely. On a given
        // iteration through the tokens though we don't want duplicates uses of the same macro to
        // trigger an error (since it's not recursive) so defer adding them to the real set until
        // next round.
        SmallVectorSized<DefineDirectiveSyntax*, 8> nextRoundAlreadyExpanded;

        // loop through each token in the replacement list and expand it if it's a nested macro
        Token token;
        while ((token = parser.next())) {
            if (token.kind != TokenKind::Directive ||
                token.directiveKind() != SyntaxKind::MacroUsage) {
                currentBuffer->append(token);
            }
            else {
                // lookup the macro definition
                auto macro = findMacro(token);
                if (!macro.valid()) {
                    // If we couldn't find the macro, just keep trucking.
                    // It's possible that a future expansion will make this valid.
                    currentBuffer->append(token);
                    continue;
                }

                if (!macro.isIntrinsic() && alreadyExpanded.count(macro.syntax)) {
                    addDiag(DiagCode::RecursiveMacro, token.location()) << token.valueText();
                    return false;
                }

                // parse arguments if necessary
                MacroActualArgumentListSyntax* actualArgs = nullptr;
                if (macro.needsArgs()) {
                    actualArgs = parser.parseActualArgumentList();
                    if (!actualArgs)
                        return false;
                }

                MacroExpansion expansion{ alloc, *currentBuffer, token, false };
                if (!expandMacro(macro, expansion, actualArgs))
                    return false;

                nextRoundAlreadyExpanded.append(macro.syntax);
                expandedSomething = true;
            }
        }

        // keep shaking until there's no more noise!
        alreadyExpanded.insert(nextRoundAlreadyExpanded.begin(), nextRoundAlreadyExpanded.end());
        tokens = span<Token const>(currentBuffer->begin(), currentBuffer->end());
        std::swap(currentBuffer, nextBuffer);
        currentBuffer->clear();

    } while (expandedSomething);

    // Make a heap copy of the tokens before we leave
    tokens = nextBuffer->copy(alloc);
    return true;
}

bool Preprocessor::expandIntrinsic(MacroIntrinsic intrinsic, MacroExpansion& expansion) {
    auto info = alloc.emplace<Token::Info>();
    auto loc = expansion.getRange().start();

    SmallVectorSized<char, 64> text;
    switch (intrinsic) {
        case MacroIntrinsic::File: {
            string_view fileName = sourceManager.getFileName(loc);
            text.appendRange(fileName);
            info->extra = fileName;
            info->rawText = to_string_view(text.copy(alloc));

            expansion.append(Token(TokenKind::StringLiteral, info), loc);
            break;
        }
        case MacroIntrinsic::Line: {
            uint32_t lineNum = sourceManager.getLineNumber(loc);
            text.appendRange(std::to_string(lineNum)); // not the most efficient, but whatever
            info->setInt(alloc, lineNum);
            info->rawText = to_string_view(text.copy(alloc));

            expansion.append(Token(TokenKind::IntegerLiteral, info), loc);
            break;
        }
        case MacroIntrinsic::None:
            THROW_UNREACHABLE;
    }

    return true;
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
        return Token::createExpected(alloc, diagnostics, result, kind, lastConsumed);

    lastConsumed = currentToken;
    currentToken = Token();
    return result;
}

Diagnostic& Preprocessor::addDiag(DiagCode code, SourceLocation location) {
    return diagnostics.add(code, location);
}

bool Preprocessor::MacroDef::needsArgs() const {
    return syntax && syntax->formalArguments;
}

MacroFormalArgumentListSyntax* Preprocessor::MacroParser::parseFormalArgumentList() {
    // parse all formal arguments
    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 16> arguments;
    parseArgumentList(arguments, [this]() { return parseFormalArgument(); });

    return pp.alloc.emplace<MacroFormalArgumentListSyntax>(openParen, arguments.copy(pp.alloc),
                                                           expect(TokenKind::CloseParenthesis));
}

MacroActualArgumentListSyntax* Preprocessor::MacroParser::parseActualArgumentList() {
    // macro has arguments, so we expect to see them here
    if (!peek(TokenKind::OpenParenthesis)) {
        pp.addDiag(DiagCode::ExpectedMacroArgs, peek().location());
        return nullptr;
    }

    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 16> arguments;
    parseArgumentList(arguments, [this]() { return parseActualArgument(); });

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return pp.alloc.emplace<MacroActualArgumentListSyntax>(openParen, arguments.copy(pp.alloc),
                                                           closeParen);
}

template<typename TFunc>
void Preprocessor::MacroParser::parseArgumentList(SmallVector<TokenOrSyntax>& results,
                                                  TFunc&& parseItem) {
    while (true) {
        results.append(parseItem());

        if (peek().kind == TokenKind::Comma)
            results.append(consume());
        else {
            // Just break out of the loop. Our caller will expect
            // that there is a closing parenthesis here.
            break;
        }
    }
}

MacroActualArgumentSyntax* Preprocessor::MacroParser::parseActualArgument() {
    auto arg = parseTokenList(true);
    return pp.alloc.emplace<MacroActualArgumentSyntax>(arg);
}

MacroFormalArgumentSyntax* Preprocessor::MacroParser::parseFormalArgument() {
    Token arg = peek();
    if (arg.kind == TokenKind::Identifier || isKeyword(arg.kind))
        consume();
    else
        arg = expect(TokenKind::Identifier);

    MacroArgumentDefaultSyntax* argDef = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        argDef = pp.alloc.emplace<MacroArgumentDefaultSyntax>(equals, parseTokenList(false));
    }

    return pp.alloc.emplace<MacroFormalArgumentSyntax>(arg, argDef);
}

span<Token> Preprocessor::MacroParser::parseTokenList(bool allowNewlines) {
    // comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}
    // otherwise, keep swallowing tokens as part of the default
    SmallVectorSized<Token, 64> tokens;
    SmallVectorSized<TokenKind, 16> delimPairStack;
    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || (!allowNewlines && !isOnSameLine(peek()))) {
            if (!delimPairStack.empty()) {
                pp.addDiag(DiagCode::UnbalancedMacroArgDims, tokens.back().location())
                    << getTokenKindText(delimPairStack.back());
            }
            break;
        }

        if (delimPairStack.empty()) {
            if ((kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis))
                break;
        }
        else if (delimPairStack.back() == kind)
            delimPairStack.pop();

        tokens.append(consume());
        switch (kind) {
            case TokenKind::OpenParenthesis:
                delimPairStack.append(TokenKind::CloseParenthesis);
                break;
            case TokenKind::OpenBrace:
                delimPairStack.append(TokenKind::CloseBrace);
                break;
            case TokenKind::OpenBracket:
                delimPairStack.append(TokenKind::CloseBracket);
                break;
            default:
                break;
        }
    }
    return tokens.copy(pp.alloc);
}

void Preprocessor::MacroParser::setBuffer(span<Token const> newBuffer) {
    buffer = newBuffer;
    currentIndex = 0;
}

Token Preprocessor::MacroParser::next() {
    if (currentIndex < buffer.size())
        return buffer[currentIndex++];
    return Token();
}

Token Preprocessor::MacroParser::peek() {
    if (currentIndex < buffer.size())
        return buffer[currentIndex];
    return pp.peek();
}

Token Preprocessor::MacroParser::consume() {
    auto result = next();
    if (result)
        return result;
    return pp.consume();
}

Token Preprocessor::MacroParser::expect(TokenKind kind) {
    if (currentIndex >= buffer.size())
        return pp.expect(kind);

    if (buffer[currentIndex].kind != kind) {
        Token last = currentIndex > 0 ? buffer[currentIndex - 1] : Token();
        return Token::createExpected(pp.alloc, pp.diagnostics, buffer[currentIndex], kind, last);
    }
    return next();
}

} // namespace slang
