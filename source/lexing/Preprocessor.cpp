//------------------------------------------------------------------------------
// Preprocessor.cpp
// SystemVerilog preprocessor and directive support.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "Preprocessor.h"

#include "parsing/AllSyntax.h"
#include "text/SourceManager.h"
#include "util/BumpAllocator.h"

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

}

namespace slang {

SyntaxKind getDirectiveKind(string_view directive);

Preprocessor::Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceManager(sourceManager),
    alloc(alloc),
    diagnostics(diagnostics)
{
    keywordVersionStack.push_back(KeywordVersion::v1800_2012);
    resetAllDirectives();
    undefineAll();
}

void Preprocessor::pushSource(string_view source) {
    auto buffer = sourceManager.assignText(source);
    pushSource(buffer);
}

void Preprocessor::pushSource(SourceBuffer buffer) {
    ASSERT(lexerStack.size() < MaxIncludeDepth);
    ASSERT(buffer.id);

    auto lexer = alloc.emplace<Lexer>(buffer, alloc, diagnostics);
    lexerStack.push_back(lexer);
}

void Preprocessor::predefine(string_view definition, string_view fileName) {
    std::string text = "`define " + string(definition) + "\n";

    Preprocessor pp(sourceManager, alloc, diagnostics);
    pp.pushSource(sourceManager.assignText(fileName, string_view(text)));
    pp.undefineAll();

    // Consume all of the definition text.
    while (pp.next().kind != TokenKind::EndOfFile) {}

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
    Token token = next(LexerMode::Normal);
    ASSERT(token);
    return token;
}

Token Preprocessor::next(LexerMode mode) {
    // The core preprocessing routine; this method pulls raw tokens from various text
    // files and converts them into a unified logical stream of sanitized tokens that
    // future stages like a parser can ingest without difficulty.
    //
    // Start off by grabbing the next raw token, either from the current file, an
    // active include file, or an expanded macro.
    auto token = nextRaw(mode);

    // If we're currently within a macro body, return whatever we got right away.
    // If it was a directive it will be deferred until the macro is used.
    if (inMacroBody)
        return token;

    // If we found a directive token, process it and pull another. We don't want
    // to return directives to the caller; we handle them ourselves and turn them
    // into trivia.
    if (token.kind == TokenKind::Directive)
        token = handleDirectives(mode, token);

    // There is an additional complication to handle; if the next raw token is right
    // next to this one (no whitespace) and is a macro expansion or include, we may
    // need to end up concatenating two tokens together before we return this one.
    // For example:
    //      `define FOO 9
    //      int i = 8`FOO;
    // This should result in "int i = 89", where the '89' is one integer token.
    if (mode == LexerMode::Normal && token.kind != TokenKind::EndOfFile) {
        lookaheadToken = nextRaw(mode);
        if (lookaheadToken.kind == TokenKind::Directive)
            token = handlePossibleConcatenation(mode, token, lookaheadToken);
    }

    return token;
}

Token Preprocessor::handleDirectives(LexerMode mode, Token token) {
    // burn through any preprocessor directives we find and convert them to trivia
    SmallVectorSized<Trivia, 16> trivia;
    do {
        switch (token.directiveKind()) {
            case SyntaxKind::IncludeDirective: trivia.append(handleIncludeDirective(token)); break;
            case SyntaxKind::ResetAllDirective: trivia.append(handleResetAllDirective(token)); break;
            case SyntaxKind::DefineDirective: trivia.append(handleDefineDirective(token)); break;
            case SyntaxKind::MacroUsage: trivia.append(handleMacroUsage(token)); break;
            case SyntaxKind::IfDefDirective: trivia.append(handleIfDefDirective(token, false)); break;
            case SyntaxKind::IfNDefDirective: trivia.append(handleIfDefDirective(token, true)); break;
            case SyntaxKind::ElsIfDirective: trivia.append(handleElsIfDirective(token)); break;
            case SyntaxKind::ElseDirective: trivia.append(handleElseDirective(token)); break;
            case SyntaxKind::EndIfDirective: trivia.append(handleEndIfDirective(token)); break;
            case SyntaxKind::TimescaleDirective: trivia.append(handleTimescaleDirective(token)); break;
            case SyntaxKind::DefaultNetTypeDirective: trivia.append(handleDefaultNetTypeDirective(token)); break;
            case SyntaxKind::LineDirective: trivia.append(handleLineDirective(token)); break;
            case SyntaxKind::UndefDirective: trivia.append(handleUndefDirective(token)); break;
            case SyntaxKind::UndefineAllDirective: trivia.append(handleUndefineAllDirective(token)); break;
            case SyntaxKind::BeginKeywordsDirective: trivia.append(handleBeginKeywordsDirective(token)); break;
            case SyntaxKind::EndKeywordsDirective: trivia.append(handleEndKeywordsDirective(token)); break;
            case SyntaxKind::PragmaDirective: // TODO, support pragmas
            case SyntaxKind::UnconnectedDriveDirective: // Nothing to do for the rest of these
            case SyntaxKind::NoUnconnectedDriveDirective:
            case SyntaxKind::CellDefineDirective:
            case SyntaxKind::EndCellDefineDirective:
            default:
                // TODO:
                // default can be reached in certain error cases
                trivia.append(createSimpleDirective(token));
                break;
        }
        token = nextRaw(mode);
    } while (token.kind == TokenKind::Directive);

    trivia.appendRange(token.trivia());
    return token.withTrivia(alloc, trivia.copy(alloc));
}

Token Preprocessor::handlePossibleConcatenation(LexerMode mode, Token left, Token right) {
    while (true) {
        // Only perform concatenation if the next upcoming token is a macro usage
        // or include directive and there is no trivia in the way.
        if (!right.trivia().empty())
            return left;

        if (right.directiveKind() != SyntaxKind::MacroUsage && right.directiveKind() != SyntaxKind::IncludeDirective)
            return left;

        lookaheadToken = Token();
        right = handleDirectives(mode, right);

        Token result = Lexer::concatenateTokens(alloc, left, right);
        if (!result) {
            // Failed to concatenate; put the token back and deal with it later.
            lookaheadToken = right;
            return left;
        }

        left = result;
        right = lookaheadToken = nextRaw(mode);
        if (lookaheadToken.kind != TokenKind::Directive)
            return left;
    }
}

Token Preprocessor::nextRaw(LexerMode mode) {
    // it's possible we have a token buffered from looking ahead when handling a directive
    if (currentToken)
        return std::exchange(currentToken, Token());
    if (lookaheadToken)
        return std::exchange(lookaheadToken, Token());

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
    auto token = source->lex(mode, keywordVersionStack.back());
    if (token.kind != TokenKind::EndOfFile) {
        // The idea here is that if we have more things on the stack,
        // the current lexer must be for an include file
        if (lexerStack.size() > 1)
            token = token.asPreprocessed(alloc);
        return token;
    }

    // don't return EndOfFile tokens for included files, fall
    // through to loop to merge trivia
    lexerStack.pop_back();
    if (lexerStack.empty())
        return token;

    // Rare case: we have an EoF from an include file... we don't want to
    // return that one, but we do want to merge its trivia with whatever comes
    // next.
    SmallVectorSized<Trivia, 16> trivia;
    trivia.appendRange(token.trivia());

    while (true) {
        auto& nextSource = lexerStack.back();
        token = nextSource->lex(mode, keywordVersionStack.back());
        trivia.appendRange(token.trivia());
        if (token.kind != TokenKind::EndOfFile)
            break;

        lexerStack.pop_back();
        if (lexerStack.empty())
            break;
    }

    // finally found a real token to return, so update trivia and get out of here
    token = token.withTrivia(alloc, trivia.copy(alloc));
    if (lexerStack.size() > 1)
        token = token.asPreprocessed(alloc);
    return token;
}

Trivia Preprocessor::handleIncludeDirective(Token directive) {
    // next token should be a filename, or something the preprocessor generated
    // that we will make into a filename
    Token fileName = next(LexerMode::IncludeFileName);

    // If we have a macro-expanded filename, there won't be an EOD token
    bool suppressEODError = false;
    if (fileName.kind != TokenKind::IncludeFileName) {
        suppressEODError = true;

        // A raw include file name will always yield a IncludeFileName token.
        // A (valid) macro-expanded include filename will be lexed as either
        // a StringLiteral or the token sequence '<' ... '>'
        if (fileName.kind == TokenKind::LessThan) {
            // In this case, we know that the first token is LessThan, and
            // if things are proper, the last token is >, but there can be an
            // arbitrary number of tokens that the macro expanded to in-between
            // (as file names have no restrictions like identifiers do)
            // so let us now concatenate all of the tokens from the macro expansion
            // up to the '>'' in order to get the file name.
            SourceLocation rootExpansionLoc = sourceManager.getExpansionLoc(fileName.location());
            SmallVectorSized<Token, 8> tokens;
            tokens.append(fileName);
            Token nextToken = peek();
            while (nextToken.kind != TokenKind::GreaterThan) {
                if (sourceManager.getExpansionLoc(nextToken.location()) != rootExpansionLoc) {
                    addError(DiagCode::ExpectedIncludeFileName, fileName.location());
                    break;
                }
                consume();
                tokens.append(nextToken);
                nextToken = peek();
                if (nextToken.kind == TokenKind::GreaterThan) {
                    tokens.append(nextToken);
                    fileName = Lexer::stringify(alloc, fileName.location(), fileName.trivia(),
                                                tokens.begin(), tokens.end(), true);
                    fileName.kind = TokenKind::IncludeFileName;
                }
            }
        }
        else if (fileName.kind == TokenKind::StringLiteral) {
            uint32_t len = (uint32_t)fileName.valueText().length();
            char* stringBuffer = (char*)alloc.allocate(len + 3);
            stringBuffer[0] = '"';
            fileName.valueText().copy(stringBuffer + 1, len);
            stringBuffer[len + 1] = '"';
            stringBuffer[len + 2] = '\0';

            auto fileNameInfo = alloc.emplace<Token::Info>(fileName.trivia(),
                fileName.rawText(), fileName.location(), fileName.getInfo()->flags);

            fileNameInfo->extra = string_view(stringBuffer, len + 2);
            fileName = Token(TokenKind::IncludeFileName, fileNameInfo);
        }
        else {
            addError(DiagCode::ExpectedIncludeFileName, fileName.location());
        }
    }

    Token end = parseEndOfDirective(suppressEODError);

    // path should be at least three chars: "a" or <a>
    string_view path = fileName.valueText();
    if (path.length() < 3)
        addError(DiagCode::ExpectedIncludeFileName, fileName.location());
    else {
        // remove delimiters
        bool isSystem = path[0] == '<';
        path = path.substr(1, path.length() - 2);
        SourceBuffer buffer = sourceManager.readHeader(path, directive.location(), isSystem);
        if (!buffer.id)
            addError(DiagCode::CouldNotOpenIncludeFile, fileName.location());
        else if (lexerStack.size() >= MaxIncludeDepth)
            addError(DiagCode::ExceededMaxIncludeDepth, fileName.location());
        else
            pushSource(buffer);
    }

    auto syntax = alloc.emplace<IncludeDirectiveSyntax>(directive, fileName, end);
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
            addError(DiagCode::InvalidMacroName, name.location());
        else {
            // check if this is a function-like macro, which requires an opening paren with no leading space
            if (peek(TokenKind::OpenParenthesis) && peek().trivia().empty()) {
                MacroParser parser(*this);
                formalArguments = parser.parseFormalArgumentList();
            }
            noErrors = true;
        }
    }

    // consume all remaining tokens as macro text
    bool needEod = false;
    scratchTokenBuffer.clear();
    while (!peek(TokenKind::EndOfDirective)) {
        // In SystemVerilog macros can actually contain other directives, such as ifdef. We
        // therefore have to keep track of where EndOfDirective tokens need to be so that
        // when the macro gets expanded they parse correctly.
        Token t = peek();
        if (needEod && (t.hasTrivia(TriviaKind::EndOfLine) || t.hasTrivia(TriviaKind::LineContinuation))) {
            scratchTokenBuffer.append(Token(TokenKind::EndOfDirective, alloc.emplace<Token::Info>()));
            needEod = false;
        }

        if (t.kind == TokenKind::Directive && t.directiveKind() != SyntaxKind::MacroUsage)
            needEod = true;

        scratchTokenBuffer.append(consume());
    }
    inMacroBody = false;

    if (needEod)
        scratchTokenBuffer.append(Token(TokenKind::EndOfDirective, alloc.emplace<Token::Info>()));

    auto result = alloc.emplace<DefineDirectiveSyntax>(
        directive,
        name,
        formalArguments,
        scratchTokenBuffer.copy(alloc),
        consume()
    );

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

    branchStack.push_back(BranchEntry(take));

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

bool Preprocessor::shouldTakeElseBranch(SourceLocation location, bool isElseIf, string_view macroName) {
    // empty stack is an error
    if (branchStack.empty()) {
        addError(DiagCode::UnexpectedConditionalDirective, location);
        return true;
    }

    // if we already had an else for this branch, we can't have any more elseifs
    BranchEntry& branch = branchStack.back();
    if (branch.hasElse) {
        addError(DiagCode::UnexpectedConditionalDirective, location);
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
    auto eod = parseEndOfDirective();
    scratchTokenBuffer.clear();
    if (!taken) {
        // skip over everything until we find another conditional compilation directive
        while (true) {
            auto token = nextRaw(LexerMode::Normal);

            // EoF or conditional directive stops the skipping process
            bool done = false;
            if (token.kind == TokenKind::EndOfFile)
                done = true;
            else if (token.kind == TokenKind::Directive) {
                switch (token.directiveKind()) {
                    // we still need to handle line continuations correctly for macro defines
                    case SyntaxKind::DefineDirective:
                        do {
                            scratchTokenBuffer.append(token);
                            token = nextRaw(LexerMode::Directive);
                        } while (token.kind != TokenKind::EndOfDirective);
                        break;

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
            directive.directiveKind(),
            directive,
            condition,
            eod,
            scratchTokenBuffer.copy(alloc)
        );
    }
    else {
        syntax = alloc.emplace<UnconditionalBranchDirectiveSyntax>(
            directive.directiveKind(),
            directive,
            eod,
            scratchTokenBuffer.copy(alloc)
        );
    }
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleEndIfDirective(Token directive) {
    // pop the active branch off the stack
    bool taken = true;
    if (branchStack.empty())
        addError(DiagCode::UnexpectedConditionalDirective, directive.location());
    else {
        branchStack.pop_back();
        if (!branchStack.empty() && !branchStack.back().currentActive)
            taken = false;
    }
    return parseBranchDirective(directive, Token(), taken);
}

bool Preprocessor::expectTimescaleSpecifier(Token& value, Token& unit, TimescaleMagnitude& magnitude) {
    auto token = peek();
    if (token.kind == TokenKind::IntegerLiteral) {
        value = consume();
        unit = expect(TokenKind::Identifier);

        string_view unused;
        std::optional<uint32_t> v = value.intValue().as<uint32_t>();
        return v && checkTimeMagnitude(*v, unused, magnitude);
    }

    if (token.kind == TokenKind::TimeLiteral) {
        // So long as we are dealing with a time literal, we should consume and
        // output the split tokens, even though those split tokens might be
        // invalid if the data is poorly formated, i.e with a number other than 1,10,100
        string_view numText;
        bool success = checkTimeMagnitude(token.realValue(), numText, magnitude);

        // generate the tokens that come from splitting the TimeLiteral
        auto valueInfo = alloc.emplace<Token::Info>(token.trivia(),
            numText, token.location(), token.getInfo()->flags);
        value = Token(TokenKind::IntegerLiteral, valueInfo);
        valueInfo->setInt(alloc, SVInt(32, (int)token.realValue(), true));

        string_view timeUnitSuffix = timeUnitToSuffix(token.numericFlags().unit());
        Token::Info* unitInfo = alloc.emplace<Token::Info>(token.trivia(),
            timeUnitSuffix, token.location() + numText.length(), token.getInfo()->flags);

        unit = Token(TokenKind::Identifier, unitInfo);
        unitInfo->extra = IdentifierType::Normal;

        consume();
        if (!success)
            addError(DiagCode::InvalidTimescaleSpecifier, token.location());
        return success;
    }

    value = Token::createExpected(alloc, diagnostics, token, TokenKind::IntegerLiteral, lastConsumed);
    unit  = Token::createExpected(alloc, diagnostics, token, TokenKind::Identifier, lastConsumed);
    return false;
}

Trivia Preprocessor::handleTimescaleDirective(Token directive) {
    Token value, valueUnit, precision, precisionUnit;
    TimescaleMagnitude valueMagnitude, precisionMagnitude;
    bool foundSpecifiers = expectTimescaleSpecifier(value, valueUnit, valueMagnitude);

    auto slash = expect(TokenKind::Slash);
    foundSpecifiers |= expectTimescaleSpecifier(precision, precisionUnit, precisionMagnitude);

    auto eod = parseEndOfDirective();

    if (foundSpecifiers) {
        TimeUnit unitValue, unitPrecision;
        bool success1 = suffixToTimeUnit(valueUnit.valueText(), unitValue);
        bool success2 = suffixToTimeUnit(precisionUnit.valueText(), unitPrecision);

        // both unit and precision must have valid units, and
        // the precision must be at least as precise as the value.
        // larger values of TimeUnit are more precise than smaller values
        if (!success1 || !success2 || unitPrecision < unitValue ||
                (unitPrecision == unitValue &&
                precision.intValue() > value.intValue())) {
            addError(DiagCode::InvalidTimescaleSpecifier, directive.location());
        }
        else {
            activeTimescale = Timescale(TimescaleValue(unitValue, valueMagnitude),
                                        TimescaleValue(unitPrecision, precisionMagnitude));
        }
    }
    auto timescale = alloc.emplace<TimescaleDirectiveSyntax>(directive, value, valueUnit, slash,
                                                             precision, precisionUnit, eod);
    return Trivia(TriviaKind::Directive, timescale);
}

Trivia Preprocessor::handleLineDirective(Token directive) {
    Token lineNumber = expect(TokenKind::IntegerLiteral);
    Token fileName = expect(TokenKind::StringLiteral);
    Token level = expect(TokenKind::IntegerLiteral);

    auto result = alloc.emplace<LineDirectiveSyntax>(directive, lineNumber, fileName,
                                                     level, parseEndOfDirective());

    if (!lineNumber.isMissing() && !fileName.isMissing() && !level.isMissing()) {
        std::optional<uint8_t> levNum = level.intValue().as<uint8_t>();
        std::optional<uint32_t> lineNum = lineNumber.intValue().as<uint32_t>();

        if (!levNum || (levNum != 0 && levNum != 1 && levNum != 2)) {
            // We don't actually use the level for anything, but the spec allows
            // only the values 0,1,2
            addError(DiagCode::InvalidLineDirectiveLevel, level.location());
        }
        else if (lineNum) {
            // We should only notify the source manager about the line directive if it
            // is well formed, to avoid very strange line number issues.
            sourceManager.addLineDirective(directive.location(),
                *lineNum, fileName.valueText(), *levNum);
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
        addError(DiagCode::ExpectedNetType, peek().location());
        netType = Token::createMissing(alloc, TokenKind::WireKeyword, peek().location());
    }

    auto result = alloc.emplace<DefaultNetTypeDirectiveSyntax>(directive, netType, parseEndOfDirective());
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
                addError(DiagCode::UndefineBuiltinDirective, nameToken.location());
        }
    }

    auto result = alloc.emplace<UndefDirectiveSyntax>(directive, nameToken, parseEndOfDirective());
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
            addError(DiagCode::UnrecognizedKeywordVersion, versionToken.location());
        else
            keywordVersionStack.push_back(*versionOpt);
    }

    auto result = alloc.emplace<BeginKeywordsDirectiveSyntax>(directive, versionToken, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleEndKeywordsDirective(Token directive) {
    if (keywordVersionStack.size() == 1)
        addError(DiagCode::MismatchedEndKeywordsDirective, directive.location());
    else
        keywordVersionStack.pop_back();

    return createSimpleDirective(directive);
}

Token Preprocessor::parseEndOfDirective(bool suppressError) {
    // consume all extraneous tokens as SkippedToken trivia
    SmallVectorSized<Token, 32> skipped;
    if (!peek(TokenKind::EndOfDirective)) {
        if (!suppressError)
            addError(DiagCode::ExpectedEndOfDirective, peek().location());
        do {
            skipped.append(consume());
        } while (!peek(TokenKind::EndOfDirective));
    }

    Token eod = consume();
    if (!skipped.empty()) {
        // splice together the trivia
        SmallVectorSized<Trivia, 16> trivia;
        trivia.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
        trivia.appendRange(eod.trivia());
        eod = eod.withTrivia(alloc, trivia.copy(alloc));
    }

    return eod;
}

Trivia Preprocessor::createSimpleDirective(Token directive, bool suppressError) {
    DirectiveSyntax* syntax = alloc.emplace<SimpleDirectiveSyntax>(
        directive.directiveKind(), directive, parseEndOfDirective(suppressError));

    return Trivia(TriviaKind::Directive, syntax);
}

Preprocessor::MacroDef Preprocessor::findMacro(Token directive) {
    auto it = macros.find(directive.valueText().substr(1));
    if (it == macros.end())
        return nullptr;
    return it->second;
}

MacroActualArgumentListSyntax* Preprocessor::handleTopLevelMacro(Token directive) {
    // if this assert fires, we failed to fully expand nested macros at a previous point
    ASSERT(!currentMacroToken);

    auto macro = findMacro(directive);
    if (!macro.valid()) {
        addError(DiagCode::UnknownDirective, directive.location()) << directive.valueText();

        // If we see a parenthesis next, let's assume they tried to invoke a function-like macro
        // and skip over the tokens.
        if (peek(TokenKind::OpenParenthesis, LexerMode::Normal))
            return MacroParser(*this).parseActualArgumentList();
        return nullptr;
    }

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (macro.needsArgs()) {
        actualArgs = MacroParser(*this).parseActualArgumentList();
        if (!actualArgs)
            return nullptr;
    }

    // Expand out the macro
    SmallVectorSized<Token, 32> buffer;
    if (!expandMacro(macro, directive, actualArgs, buffer))
        return actualArgs;

    // The macro is now expanded out into tokens, but some of those tokens might
    // be more macros that need to be expanded, or special characters that
    // perform stringification or concatenation of tokens. It's possible that
    // after concatentation is performed we will have formed new valid macro
    // names that need to be expanded, which is why we loop here.
    span<Token const> tokens = buffer.copy(alloc);
    while (true) {
        // Start by recursively expanding out all valid macro usages.
        if (!expandReplacementList(tokens))
            return actualArgs;

        // Now that all macros have been expanded, handle token concatenation and stringification.
        SmallVectorSized<Trivia, 16> emptyArgTrivia;
        Token stringify;
        buffer.clear();
        expandedTokens.clear();
        bool anyNewMacros = false;

        for (uint32_t i = 0; i < tokens.size(); i++) {
            Token newToken;

            // Once we see a `" token, we start collecting tokens into their own
            // buffer for stringification. Otherwise, just add them to the final
            // expansion buffer.
            Token token = tokens[i];
            switch (token.kind) {
                case TokenKind::MacroQuote:
                    if (!stringify)
                        stringify = token;
                    else {
                        // all done stringifying; convert saved tokens to string
                        newToken = Lexer::stringify(alloc, stringify.location(),
                                                    stringify.trivia(),
                                                    buffer.begin(), buffer.end());
                        stringify = Token();
                    }
                    break;
                case TokenKind::MacroPaste:
                    // Paste together previous token and next token; a macro paste on either end
                    // of the buffer or one that borders whitespace should be ignored.
                    // This isn't specified in the standard so I'm just guessing.
                    if (i == 0 || i == tokens.size() - 1 || !token.trivia().empty() ||
                        !tokens[i + 1].trivia().empty()) {

                        addError(DiagCode::IgnoredMacroPaste, token.location());
                    }
                    else if (stringify) {
                        // if this is right after the opening quote or right before the closing quote, we're
                        // trying to concatenate something with nothing, so assume an error
                        if (buffer.empty() || tokens[i + 1].kind == TokenKind::MacroQuote)
                            addError(DiagCode::IgnoredMacroPaste, token.location());
                        else {
                            newToken = Lexer::concatenateTokens(alloc, buffer.back(), tokens[i + 1]);
                            if (newToken) {
                                buffer.pop();
                                ++i;
                            }
                        }
                    }
                    else {
                        newToken = Lexer::concatenateTokens(alloc, expandedTokens.back(), tokens[i + 1]);
                        if (newToken) {
                            expandedTokens.pop();
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

            if (newToken) {
                // If we have an empty macro argument just collect its trivia and use it on the next token we find.
                if (newToken.kind == TokenKind::EmptyMacroArgument)
                    emptyArgTrivia.appendRange(newToken.trivia());
                else {
                    if (!emptyArgTrivia.empty()) {
                        emptyArgTrivia.appendRange(newToken.trivia());
                        newToken = newToken.withTrivia(alloc, emptyArgTrivia.copy(alloc));
                        emptyArgTrivia.clear();
                    }

                    // TODO: error if no closing quote
                    if (stringify)
                        buffer.append(newToken);
                    else
                        expandedTokens.append(newToken);
                }
            }
        }

        if (!anyNewMacros)
            break;

        tokens = expandedTokens;
    }

    if (!expandedTokens.empty()) {
        // Verify that we haven't failed to expand any nested macros.
        for (Token token : expandedTokens) {
            if (token.kind == TokenKind::Directive && token.directiveKind() == SyntaxKind::MacroUsage) {
                addError(DiagCode::UnknownDirective, token.location()) << token.valueText();
                return actualArgs;
            }
        }

        // if the macro expanded into any tokens at all, set the pointer
        // so that we'll pull from them next
        currentMacroToken = expandedTokens.begin();
    }

    return actualArgs;
}

bool Preprocessor::expandMacro(MacroDef macro, Token usageSite, MacroActualArgumentListSyntax* actualArgs,
                               SmallVector<Token>& dest) {
    if (macro.isIntrinsic()) {
        // for now, no intrisics can have arguments
        ASSERT(!actualArgs);
        return expandIntrinsic(macro.intrinsic, usageSite, dest);
    }

    DefineDirectiveSyntax* directive = macro.syntax;
    ASSERT(directive);

    // ignore empty macro
    const auto& body = directive->body;
    if (body.count() == 0)
        return true;

    if (!directive->formalArguments) {
        // each macro expansion gets its own location entry
        SourceLocation start = body[0].location();
        SourceLocation usageLoc = usageSite.location();
        SourceLocation expansionLoc = sourceManager.createExpansionLoc(
            start,
            usageLoc,
            usageLoc + usageSite.rawText().length()
        );

        // simple macro; just take body tokens
        bool isFirst = true;
        for (auto& token : body)
            appendBodyToken(dest, token, start, expansionLoc, usageSite, isFirst);
        return true;
    }

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = directive->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.count() > formalList.count()) {
        addError(DiagCode::TooManyActualMacroArgs, actualArgs->getFirstToken().location());
        return false;
    }

    argumentMap.clear();
    for (uint32_t i = 0; i < formalList.count(); i++) {
        auto formal = formalList[i];
        auto name = formal->name.valueText();

        const TokenList* tokenList = nullptr;
        if (actualList.count() > i) {
            // if our actual argument is empty and we have a default, take that
            tokenList = &actualList[i]->tokens;
            if (tokenList->count() == 0 && formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
        }
        else {
            // if we've run out of actual args make sure we have a default for this one
            if (formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
            else {
                addError(DiagCode::NotEnoughMacroArgs, actualArgs->closeParen.location());
                return false;
            }
        }

        // The C preprocessor would fully pre-expand and mark any macro usage in the arguments here;
        // because SystemVerilog macros are different tokens than identifiers (backtick character differentiates)
        // we don't have to bother doing that. All macros either fully expand or we have an error if we detect
        // recursive usage.
        argumentMap[name] = tokenList;
    }

    // TODO: the expansion range for a function-like macro should include the parenthesis and arguments
    SourceLocation start = body[0].location();
    SourceLocation usageLoc = usageSite.location();
    SourceLocation expansionLoc = sourceManager.createExpansionLoc(
        start,
        usageLoc,
        usageLoc + usageSite.rawText().length()
    );

    // now add each body token, substituting arguments as necessary
    bool isFirst = true;
    for (auto& token : body) {
        if (token.kind != TokenKind::Identifier && !isKeyword(token.kind) &&
            (token.kind != TokenKind::Directive || token.directiveKind() != SyntaxKind::MacroUsage)) {
            appendBodyToken(dest, token, start, expansionLoc, usageSite, isFirst);
        }
        else {
            // Other tools allow arguments to replace matching directive names, e.g.:
            // `define FOO(bar) `bar
            // `define ONE 1
            // `FOO(ONE)   // expands to 1
            string_view text = token.valueText();
            if (token.kind == TokenKind::Directive)
                text = text.substr(1);

            // check for formal param
            auto it = argumentMap.find(text);
            if (it == argumentMap.end())
                appendBodyToken(dest, token, start, expansionLoc, usageSite, isFirst);
            else {
                // We need to ensure that we get correct spacing for the leading token here;
                // it needs to come from the *formal* parameter used in the macro body, not
                // from the argument itself.
                auto begin = it->second->begin();
                auto end = it->second->end();
                if (begin != end) {
                    // See note above about weird macro usage being argument replaced.
                    // In that case we want to fabricate the correct directive token here.
                    Token first = begin->withTrivia(alloc, token.trivia());
                    if (token.kind == TokenKind::Directive) {
                        Token grave { TokenKind::Directive, alloc.emplace<Token::Info>(
                            first.trivia(), "`", first.location(), 0) };

                        first = Lexer::concatenateTokens(alloc, grave, first);
                    }

                    appendBodyToken(dest, first, first.location(), first.location(), usageSite, isFirst);
                    for (++begin; begin != end; begin++)
                        appendBodyToken(dest, *begin, begin->location(), begin->location(), usageSite, isFirst);
                }
                else {
                    // The macro argument contained no tokens. We still need to supply an empty token
                    // here to ensure that the trivia of the formal parameter is passed on.
                    appendBodyToken(dest, Token(TokenKind::EmptyMacroArgument, token.getInfo()),
                                    start, expansionLoc, usageSite, isFirst);
                }
            }
        }
    }

    return true;
}

void Preprocessor::appendBodyToken(SmallVector<Token>& dest, Token token, SourceLocation startLoc,
                                  SourceLocation expansionLoc, Token usageSite, bool& isFirst) {
    int delta = token.location().offset() - startLoc.offset();
    if (isFirst) {
        token = token.withTrivia(alloc, usageSite.trivia());
        isFirst = false;

        // If our usageSite had no whitespace, we should concatenate with whatever was previously in the buffer.
        if (usageSite.trivia().empty() && !dest.empty()) {
            Token concat = Lexer::concatenateTokens(alloc, dest.back(), token);
            if (concat) {
                dest.back() = concat;
                return;
            }
        }
    }
    dest.append(token.withLocation(alloc, expansionLoc + delta));
}

bool Preprocessor::expandReplacementList(span<Token const>& tokens) {
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

        // loop through each token in the replacement list and expand it if it's a nested macro
        Token token;
        while ((token = parser.next())) {
            if ((expandedSomething && token.trivia().empty()) || token.kind != TokenKind::Directive ||
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

                // parse arguments if necessary
                MacroActualArgumentListSyntax* actualArgs = nullptr;
                if (macro.needsArgs()) {
                    actualArgs = parser.parseActualArgumentList();
                    if (!actualArgs)
                        return false;
                }

                if (!expandMacro(macro, token, actualArgs, *currentBuffer))
                    return false;

                expandedSomething = true;
            }
        }

        // shake the box until the cat stops making noise
        tokens = span<Token const>(currentBuffer->begin(), currentBuffer->end());
        std::swap(currentBuffer, nextBuffer);
        currentBuffer->clear();

    } while (expandedSomething);

    // Make a heap copy of the tokens before we leave
    tokens = nextBuffer->copy(alloc);
    return true;
}

bool Preprocessor::expandIntrinsic(MacroIntrinsic intrinsic, Token usageSite, SmallVector<Token>& dest) {
    // Take the location and trivia from the usage site; the source text we're
    // going to make up here doesn't actually exist and shouldn't be shown to the
    // user as an "expanded from here" note.
    auto info = alloc.emplace<Token::Info>(usageSite.trivia(), "", usageSite.location(), 0);

    // Create a buffer to hold the raw text for the new tokens we will fabricate.
    SmallVectorSized<char, 64> text;

    switch (intrinsic) {
        case MacroIntrinsic::File: {
            string_view fileName = sourceManager.getFileName(usageSite.location());
            text.appendRange(fileName);
            info->extra = fileName;
            info->rawText = to_string_view(text.copy(alloc));

            dest.append(Token(TokenKind::StringLiteral, info));
            break;
        }
        case MacroIntrinsic::Line: {
            uint32_t lineNum = sourceManager.getLineNumber(usageSite.location());
            text.appendRange(std::to_string(lineNum)); // not the most efficient, but whatever
            info->setInt(alloc, SVInt(lineNum));
            info->rawText = to_string_view(text.copy(alloc));

            // Use appendBodyToken so that implicit concatenation will occur if something else
            // was already in the destination buffer.
            bool isFirst = true;
            appendBodyToken(dest, Token(TokenKind::IntegerLiteral, info), usageSite.location(),
                            usageSite.location(), usageSite, isFirst);
            break;
        }
        case MacroIntrinsic::None:
            THROW_UNREACHABLE;
    }

    return true;
}

Token Preprocessor::peek(LexerMode mode) {
    if (!currentToken)
        currentToken = next(mode);
    return currentToken;
}

Token Preprocessor::consume(LexerMode mode) {
    auto result = peek(mode);
    currentToken = Token();
    return result;
}

Token Preprocessor::expect(TokenKind kind, LexerMode mode) {
    auto result = peek(mode);
    if (result.kind != kind)
        return Token::createExpected(alloc, diagnostics, result, kind, lastConsumed);

    lastConsumed = currentToken;
    currentToken = Token();
    return result;
}

Diagnostic& Preprocessor::addError(DiagCode code, SourceLocation location) {
    return diagnostics.add(code, location);
}

bool Preprocessor::MacroDef::needsArgs() const {
    return syntax && syntax->formalArguments;
}

MacroFormalArgumentListSyntax* Preprocessor::MacroParser::parseFormalArgumentList() {
    // parse all formal arguments
    currentMode = LexerMode::Directive;
    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 16> arguments;
    parseArgumentList(arguments, [this]() { return parseFormalArgument(); });

    return pp.alloc.emplace<MacroFormalArgumentListSyntax>(
        openParen,
        arguments.copy(pp.alloc),
        expect(TokenKind::CloseParenthesis)
    );
}

MacroActualArgumentListSyntax* Preprocessor::MacroParser::parseActualArgumentList() {
    // macro has arguments, so we expect to see them here
    currentMode = LexerMode::Normal;
    if (!peek(TokenKind::OpenParenthesis)) {
        pp.addError(DiagCode::ExpectedMacroArgs, peek().location());
        return nullptr;
    }

    auto openParen = consume();
    SmallVectorSized<TokenOrSyntax, 16> arguments;
    parseArgumentList(arguments, [this]() { return parseActualArgument(); });

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return pp.alloc.emplace<MacroActualArgumentListSyntax>(openParen, arguments.copy(pp.alloc), closeParen);
}

template<typename TFunc>
void Preprocessor::MacroParser::parseArgumentList(SmallVector<TokenOrSyntax>& buffer, TFunc&& parseItem) {
    while (true) {
        buffer.append(parseItem());

        if (peek().kind == TokenKind::Comma)
            buffer.append(consume());
        else {
            // Just break out of the loop. Our caller will expect
            // that there is a closing parenthesis here.
            break;
        }
    }
}

MacroActualArgumentSyntax* Preprocessor::MacroParser::parseActualArgument() {
    auto arg = parseTokenList();
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
        argDef = pp.alloc.emplace<MacroArgumentDefaultSyntax>(equals, parseTokenList());
    }

    return pp.alloc.emplace<MacroFormalArgumentSyntax>(arg, argDef);
}

span<Token const> Preprocessor::MacroParser::parseTokenList() {
    // comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}
    // otherwise, keep swallowing tokens as part of the default
    SmallVectorSized<Token, 64> tokens;
    SmallVectorSized<TokenKind, 16> delimPairStack;
    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfDirective || kind == TokenKind::EndOfFile) {
            if (!delimPairStack.empty())
                pp.addError(DiagCode::UnbalancedMacroArgDims, peek().location()) << getTokenKindText(delimPairStack.back());
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
    return pp.peek(currentMode);
}

Token Preprocessor::MacroParser::consume() {
    auto result = next();
    if (result)
        return result;
    return pp.consume(currentMode);
}

Token Preprocessor::MacroParser::expect(TokenKind kind) {
    if (currentIndex >= buffer.size())
        return pp.expect(kind, currentMode);

    if (buffer[currentIndex].kind != kind) {
        Token last = currentIndex > 0 ? buffer[currentIndex - 1] : Token();
        return Token::createExpected(pp.alloc, pp.diagnostics, buffer[currentIndex], kind, last);
    }
    return next();
}

}
