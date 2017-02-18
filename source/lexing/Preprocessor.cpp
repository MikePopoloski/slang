//------------------------------------------------------------------------------
// Preprocessor.cpp
// SystemVerilog preprocessor and directive support.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "Preprocessor.h"

#include "parsing/AllSyntax.h"
#include "text/SourceManager.h"
#include "util/Debug.h"
#include "util/BumpAllocator.h"

namespace slang {

// Placeholders for __FILE__ and __LINE__ macros; these exist so that we get nice tokens
// automatically when expanding macros that we can replace with the correct values.
static Token::Info unusedTokenInfo;
static Token intrinsicFileToken = Token(TokenKind::IntrinsicFileMacro, &unusedTokenInfo);
static Token intrinsicLineToken = Token(TokenKind::IntrinsicLineMacro, &unusedTokenInfo);
static DefineDirectiveSyntax fileDirective { Token(), Token(), nullptr, ArrayRef<Token>(&intrinsicFileToken, 1), Token() };
static DefineDirectiveSyntax lineDirective { Token(), Token(), nullptr, ArrayRef<Token>(&intrinsicLineToken, 1), Token() };

SyntaxKind getDirectiveKind(StringRef directive);

Preprocessor::Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceManager(sourceManager),
    alloc(alloc),
    diagnostics(diagnostics)
{
    keywordVersionStack.push_back(KeywordVersion::v1800_2012);
    macros["__FILE__"] = &fileDirective;
    macros["__LINE__"] = &lineDirective;
}

void Preprocessor::pushSource(StringRef source) {
    auto buffer = sourceManager.assignText(source);
    pushSource(buffer);
}

void Preprocessor::pushSource(SourceBuffer buffer) {
    ASSERT(lexerStack.size() < MaxIncludeDepth);
    ASSERT(buffer.id);

    auto lexer = alloc.emplace<Lexer>(buffer, alloc, diagnostics);
    lexerStack.push_back(lexer);
}

Token Preprocessor::next() {
    Token token = next(LexerMode::Normal);
    ASSERT(token);
    return token;
}

Token Preprocessor::next(LexerMode mode) {
    // common case: lex a token and return it
    auto token = nextRaw(mode);
    if (token.kind != TokenKind::Directive || inMacroBody)
        return token;

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
            // default can be reached in certain error cases
                trivia.append(createSimpleDirective(token));
                break;
        }
        token = nextRaw(mode);
    } while (token.kind == TokenKind::Directive);

    trivia.appendRange(token.trivia());
    return token.withTrivia(alloc, trivia.copy(alloc));
}

Token Preprocessor::nextRaw(LexerMode mode) {
    // it's possible we have a token buffered from looking ahead when handling a directive
    if (currentToken) {
        auto result = currentToken;
        currentToken = Token();
        return result;
    }

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
        // a (valid) macro-expanded include filename will be lexed as either
        // a StringLiteral or the token sequence '<' ... '>'
        bool angleBrackets = false;
        if (fileName.kind == TokenKind::LessThan) {
            angleBrackets = true;
            // In this case, we know that the first token is LessThan, and
            // if things are proper, the last token is >, but there can be an
            // arbitrary number of tokens that the macro expanded to in-between
            // (as file names have no restrictions like identifiers do)
            // so let us now concatenate all of the tokens from the macro expansion
            // up to the '>'' in order to get the file name
            SourceLocation rootExpansionLoc = sourceManager.getExpansionLoc(fileName.location());
            Token concatenatedFileName = fileName;
            SmallVectorSized<Token, 8> tokens;
            tokens.append(fileName);
            Token nextToken = peek();
            while (nextToken.kind != TokenKind::GreaterThan) {
                // TODO: we should probably stop at something like a >>, >>= token,
                // but behavior when reaching those tokens is likely to be destructive either way
                // unless you have some crazy filenames you want to include
                if (sourceManager.getExpansionLoc(nextToken.location()) != rootExpansionLoc) {
                    addError(DiagCode::ExpectedIncludeFileName, fileName.location());
                    break;
                }
                consume();
                tokens.append(nextToken);
                nextToken = peek();
                if (nextToken.kind == TokenKind::GreaterThan) {
                    tokens.append(nextToken);
                    // do stringification
                    fileName = Lexer::stringify(alloc, fileName.location(), fileName.getInfo()->trivia,
                        tokens.begin(), tokens.end(), true);
                    fileName.kind = TokenKind::IncludeFileName;
                }
            }
        } else if (fileName.kind == TokenKind::StringLiteral) {
            uint32_t len = fileName.valueText().length();
            uint8_t* stringBuffer = alloc.allocate(len + 3);
            stringBuffer[0] = '"';
            memcpy(stringBuffer + 1, fileName.valueText().begin(), len);
            stringBuffer[len + 1] = '"';
            stringBuffer[len + 2] = '\0';
            Token::Info *fileNameInfo = alloc.emplace<Token::Info>(fileName.trivia(),
                fileName.rawText(), fileName.location(), fileName.getInfo()->flags);
            fileNameInfo->extra = StringRef((const char *)stringBuffer, len + 2);
            fileName = *alloc.emplace<Token>(TokenKind::IncludeFileName, fileNameInfo);
        } else {
            addError(DiagCode::ExpectedIncludeFileName, fileName.location());
        }
    }
    Token end = parseEndOfDirective(suppressEODError);

    // path should be at least three chars: "a" or <a>
    StringRef path = fileName.valueText();

    if (path.length() < 3)
        addError(DiagCode::ExpectedIncludeFileName, fileName.location());
    else {
        // remove delimiters
        path = path.subString(1, path.length() - 2);
        SourceBuffer buffer = sourceManager.readHeader(path, directive.location(), false);
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
    // TODO: reset all preprocessor state here
    // TODO: keep track of any of the state that this resets
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
    SmallVectorSized<Token, 32> body;
    while (!peek(TokenKind::EndOfDirective)) {
        // In SystemVerilog macros can actually contain other directives, such as ifdef. We
        // therefore have to keep track of where EndOfDirective tokens need to be so that
        // when the macro gets expanded they parse correctly.
        Token t = peek();
        if (needEod && (t.hasTrivia(TriviaKind::EndOfLine) || t.hasTrivia(TriviaKind::LineContinuation))) {
            body.append(Token(TokenKind::EndOfDirective, alloc.emplace<Token::Info>()));
            needEod = false;
        }

        if (t.kind == TokenKind::Directive) {
            switch (t.directiveKind()) {
                case SyntaxKind::IfDefDirective:
                case SyntaxKind::ElseDirective:
                case SyntaxKind::IfNDefDirective:
                case SyntaxKind::ElsIfDirective:
                case SyntaxKind::EndIfDirective:
                    needEod = true;
                    break;
                default:
                    break;
            }
        }
        body.append(consume());
    }
    inMacroBody = false;

    auto result = alloc.emplace<DefineDirectiveSyntax>(
        directive,
        name,
        formalArguments,
        body.copy(alloc),
        consume()
    );

    if (noErrors)
        macros[name.valueText().intern(alloc)] = result;
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleMacroUsage(Token directive) {
    // delegate to a nested function to simplify the error handling paths
    auto actualArgs = handleTopLevelMacro(directive);
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
    bool take = shouldTakeElseBranch(directive.location(), false, nullptr);
    return parseBranchDirective(directive, Token(), take);
}

bool Preprocessor::shouldTakeElseBranch(SourceLocation location, bool isElseIf, StringRef macroName) {
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
    SmallVectorSized<Token, 32> skipped;
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
                            skipped.append(token);
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
            skipped.append(token);
        }
    }

    SyntaxNode* syntax;
    if (condition) {
        syntax = alloc.emplace<ConditionalBranchDirectiveSyntax>(
            directive.directiveKind(),
            directive,
            condition,
            eod,
            skipped.copy(alloc)
        );
    }
    else {
        syntax = alloc.emplace<UnconditionalBranchDirectiveSyntax>(
            directive.directiveKind(),
            directive,
            eod,
            skipped.copy(alloc)
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

bool Preprocessor::expectTimescaleSpecifier(Token& value, Token& unit) {
    auto token = peek();
    if (token.kind == TokenKind::IntegerLiteral) {
        value = consume();
        unit = expect(TokenKind::Identifier);
        return true;
    } else if (token.kind == TokenKind::TimeLiteral) {
        bool success = true;
        // So long as we are dealing with a time literal, we should consume and
        // output the split tokens, even though those split tokens might be
        // invalid if the data is poorly formated, i.e with a number other than
        // 1,10,100

        // get_if necessary to check for the case where there is a double TimeLiteral
        const SVInt *val = std::get_if<SVInt>(&token.numericValue());
        StringRef numText;
        if (val == nullptr) {
            // create a dummy value to place in the generated token
            val = alloc.emplace<SVInt>(16, 0, true);
            success = false;
        }
        else if (*val == 1) numText = "1";
        else if (*val == 10) numText = "10";
        else if (*val == 100) numText = "100";
        else success = false;

        // generate the tokens that come from splitting the TimeLiteral
        Token::Info* valueInfo = alloc.emplace<Token::Info>(token.trivia(),
            numText, token.location(), token.getInfo()->flags);
        value = *alloc.emplace<Token>(TokenKind::IntegerLiteral, valueInfo);
        valueInfo->setNumInfo(*val);

        StringRef timeUnitSuffix = timeUnitToSuffix(token.numericFlags().unit);
        Token::Info* unitInfo = alloc.emplace<Token::Info>(token.trivia(),
            timeUnitSuffix,
            token.location() + numText.length(), token.getInfo()->flags);
        unit = *alloc.emplace<Token>(TokenKind::Identifier, unitInfo);
        unitInfo->extra = IdentifierType::Normal;

        consume();
        if (!success) {
            addError(DiagCode::InvalidTimescaleSpecifier, token.location());
            return false;
        } else {
            return true;
        }
    } else {
        value = Token::createExpected(alloc, diagnostics, token, TokenKind::IntegerLiteral, lastConsumed);
        unit  = Token::createExpected(alloc, diagnostics, token, TokenKind::Identifier, lastConsumed);
    }
    return false;
}

Trivia Preprocessor::handleTimescaleDirective(Token directive) {
    Token value, valueUnit, precision, precisionUnit;
    bool foundSpecifiers = expectTimescaleSpecifier(value, valueUnit);

    auto slash = expect(TokenKind::Slash);
    foundSpecifiers |= expectTimescaleSpecifier(precision, precisionUnit);

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
                std::get<SVInt>(precision.numericValue()) > std::get<SVInt>(value.numericValue()))) {
            addError(DiagCode::InvalidTimescaleSpecifier, directive.location());
        }
    }
    auto timescale = alloc.emplace<TimescaleDirectiveSyntax>(directive, value, valueUnit, slash, precision, precisionUnit, eod);
    return Trivia(TriviaKind::Directive, timescale);
}

Trivia Preprocessor::handleLineDirective(Token directive) {
    Token lineNumber = expect(TokenKind::IntegerLiteral);
    Token fileName = expect(TokenKind::StringLiteral);
    Token level = expect(TokenKind::IntegerLiteral);
    const SVInt& levNum = std::get<SVInt>(level.numericValue());
    if (!(levNum == 0 || levNum == 1 || levNum == 2)) {
        // We don't actually use the level for anything, but the spec allows
        // only the values 0,1,2
        addError(DiagCode::InvalidLineDirectiveLevel, level.location());
    }
    auto result = alloc.emplace<LineDirectiveSyntax>(directive, lineNumber, fileName, level, parseEndOfDirective());
    if (!(lineNumber.isMissing() || fileName.isMissing() || level.isMissing())) {
        // We should only notify the source manager about the line directive if it
        // is well formed, to avoid very strange line number issues
        sourceManager.addLineDirective(directive.location(),
            std::get<SVInt>(lineNumber.numericValue()).getAssertUInt32(),
            fileName.valueText(), (uint8_t)levNum.getAssertUInt16());
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
            break;
        case TokenKind::Identifier:
            // none isn't a keyword but it's special here
            if (peek().rawText() == "none")
                netType = consume();
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

    // Other preprocessors consider an attempt to undef, say, `define to also
    // be an error for undefining a builtin directive, and allow undefining
    // undefined macros, making that just a warning. We instead only consider
    // __LINE__ and __FILE__ illegal to undef as builtins, and consider all
    // undefining of undefined macros to be errors.
    if (!nameToken.isMissing()) {
        StringRef name = nameToken.valueText();
        if (macros.count(name) > 0) {
            if (name != "__LINE__" && name != "__FILE__") {
                macros.erase(name);
            } else {
                addError(DiagCode::UndefineBuiltinDirective, nameToken.location());
            }
        } else {
            addError(DiagCode::UnknownDirective, nameToken.location());
        }
    } // else we add an error due to the missing token
    auto result = alloc.emplace<UndefDirectiveSyntax>(directive, nameToken, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleUndefineAllDirective(Token directive) {
    macros.clear();
    macros["__FILE__"] = &fileDirective;
    macros["__LINE__"] = &lineDirective;
    return createSimpleDirective(directive);
}

Trivia Preprocessor::handleBeginKeywordsDirective(Token directive) {
    Token versionToken = expect(TokenKind::StringLiteral);
    if (!versionToken.isMissing()) {
        StringRef verStr = versionToken.valueText();
        if (verStr == "1364-1995") {
            keywordVersionStack.push_back(KeywordVersion::v1364_1995);
        } else if (verStr == "1364-2001-noconfig") {
            keywordVersionStack.push_back(KeywordVersion::v1364_2001_noconfig);
        } else if (verStr == "1364-2001") {
            keywordVersionStack.push_back(KeywordVersion::v1364_2001);
        } else if (verStr == "1364-2005") {
            keywordVersionStack.push_back(KeywordVersion::v1364_2005);
        } else if (verStr == "1800-2005") {
            keywordVersionStack.push_back(KeywordVersion::v1800_2005);
        } else if (verStr == "1800-2009") {
            keywordVersionStack.push_back(KeywordVersion::v1800_2009);
        } else if (verStr == "1800-2012") {
            keywordVersionStack.push_back(KeywordVersion::v1800_2012);
        } else {
            // An error will already have been added if the version is missing
            addError(DiagCode::UnrecognizedKeywordVersion, versionToken.location());
        }
    }
    auto result = alloc.emplace<BeginKeywordsDirectiveSyntax>(directive, versionToken, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleEndKeywordsDirective(Token directive) {
    if (keywordVersionStack.size() == 1) {
        addError(DiagCode::MismatchedEndKeywordsDirective, directive.location());
    } else {
        keywordVersionStack.pop_back();
    }
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
    DirectiveSyntax* syntax = alloc.emplace<SimpleDirectiveSyntax>(directive.directiveKind(), directive, parseEndOfDirective(suppressError));
    return Trivia(TriviaKind::Directive, syntax);
}

DefineDirectiveSyntax* Preprocessor::findMacro(Token directive) {
    auto it = macros.find(directive.valueText().subString(1));
    if (it == macros.end()) {
        addError(DiagCode::UnknownDirective, directive.location());
        return nullptr;
    }
    return it->second;
}

MacroActualArgumentListSyntax* Preprocessor::handleTopLevelMacro(Token directive) {
    // if this assert fires, we failed to fully expand nested macros at a previous point
    ASSERT(expandedTokens.empty());

    // lookup the macro definition; findMacro will report an error for us if
    // the directive is not found
    auto definition = findMacro(directive);
    if (!definition)
        return nullptr;

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (definition->formalArguments) {
        MacroParser parser(*this);
        actualArgs = parser.parseActualArgumentList();
        if (!actualArgs)
            return actualArgs;
    }
    // TODO: if any of the actualArgs are themselves intrinsic macros, they
    // should be expanded before expanding the outer macro

    // Expand out the macro
    SmallVectorSized<Token, 32> buffer;
    if (!expandMacro(definition, directive, actualArgs, buffer))
        return actualArgs;

    // Recursively expand macros in the replacement list
    ArrayRef<Token> tokens = buffer.copy(alloc);
    if (!expandReplacementList(tokens))
        return actualArgs;

    // Now that all macros have been expanded, handle token concatenation and stringification.
    // TODO: do we have to worry about non-macros being concatenated into real macros?
    Token stringify;
    buffer.clear();
    expandedTokens.clear();
    for (uint32_t i = 0; i < tokens.count(); i++) {
        Token newToken;

        // replace intrinsic macros before we do anything else
        Token token = tokens[i];

        if (token.kind == TokenKind::IntrinsicFileMacro) {
            auto info = alloc.emplace<Token::Info>(token.trivia(), "", token.location(), 0);
            info->extra = sourceManager.getFileName(token.location());
            token = Token(TokenKind::StringLiteral, info);
        } else if (token.kind == TokenKind::IntrinsicLineMacro) {
            auto info = alloc.emplace<Token::Info>(token.trivia(), "", token.location(), 0);
            uint64_t lineNum = sourceManager.getLineNumber(token.location());
            info->setNumInfo(SVInt(lineNum));
            token = Token(TokenKind::IntegerLiteral, info);
        }

        // Once we see a `" token, we start collecting tokens into their own
        // buffer for stringification. Otherwise, just add them to the final
        // expansion buffer.
        switch (token.kind) {
            case TokenKind::MacroQuote:
                if (!stringify)
                    stringify = token;
                else {
                    // all done stringifying; convert saved tokens to string
                    newToken = Lexer::stringify(alloc, stringify.location(), stringify.trivia(), buffer.begin(), buffer.end());
                    if (!newToken) {
                        // TODO: error
                    }
                    stringify = Token();
                }
                break;
            case TokenKind::MacroEscapedQuote:
                if (!stringify) {
                    // TODO: error
                }
                else {
                    // plop this into our stringify buffer; we'll handle it later
                    newToken = token;
                }
                break;
            case TokenKind::MacroPaste:
                // Paste together previous token and next token; a macro paste on either end
                // of the buffer or one that borders whitespace should be ignored.
                // This isn't specified in the standard so I'm just guessing.
                if (i == 0 || i == tokens.count() - 1 || !token.trivia().empty() || !tokens[i+1].trivia().empty()) {
                    // TODO: warning?
                }
                else if (stringify) {
                    // if this is right after the opening quote or right before the closing quote, we're
                    // trying to concatenate something with nothing, so assume an error
                    if (buffer.empty() || tokens[i + 1].kind == TokenKind::MacroQuote) {
                        // TODO: error
                    }
                    else {
                        bool error;
                        newToken = Lexer::concatenateTokens(alloc, buffer.back(), tokens[i+1], error);
                        if (newToken) {
                            buffer.pop();
                            ++i;
                        }
                        else if (error) {
                            // TODO: handle error cases
                        }
                        // else: just discard the MacroPaste
                    }
                }
                else {
                    bool error;
                    newToken = Lexer::concatenateTokens(alloc, expandedTokens.back(), tokens[i+1], error);
                    if (newToken) {
                        expandedTokens.pop();
                        ++i;
                    }
                    else if (error) {
                        // TODO: handle error cases
                    }
                    // else: just discard the MacroPaste
                }
                break;
            default:
                newToken = token;
                break;
        }

        if (newToken) {
            // if we're stringifying, save this in a temporary buffer,
            // included saving any empty macro arguments that may have
            // important trivia. Don't pass those tokens on in a non-strinficiation
            // context though
            if (stringify)
                buffer.append(newToken);
            else if (newToken.kind != TokenKind::EmptyMacroArgument)
                expandedTokens.append(newToken);
        }
    }


    // if the macro expanded into any tokens at all, set the pointer so that we'll pull from them next
    if (!expandedTokens.empty())
        currentMacroToken = expandedTokens.begin();

    return actualArgs;
}

bool Preprocessor::expandMacro(DefineDirectiveSyntax* macro, Token usageSite, MacroActualArgumentListSyntax* actualArgs, SmallVector<Token>& dest) {
    // ignore empty macro
    if (macro->body.count() == 0)
        return true;

    if (!macro->formalArguments) {
        // each macro expansion gets its own location entry
        SourceLocation start = macro->body[0].location();
        SourceLocation usageLoc = usageSite.location();
        SourceLocation expansionLoc = sourceManager.createExpansionLoc(
            start,
            usageLoc,
            usageLoc + usageSite.rawText().length()
        );

        // simple macro; just take body tokens
        for (auto& token : macro->body) {
            int delta = token.location().offset() - start.offset();
            dest.append(token.withLocation(alloc, expansionLoc + delta));
        }
        return true;
    }

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = macro->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.count() > formalList.count()) {
        addError(DiagCode::TooManyActualMacroArgs, actualArgs->args[formalList.count()]->getFirstToken().location());
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
    SourceLocation start = macro->body[0].location();
    SourceLocation usageLoc = usageSite.location();
    SourceLocation expansionLoc = sourceManager.createExpansionLoc(
        start,
        usageLoc,
        usageLoc + usageSite.rawText().length()
    );

    // now add each body token, substituting arguments as necessary
    for (auto& token : macro->body) {
        int delta = token.location().offset() - start.offset();

        if (token.kind != TokenKind::Identifier && !isKeyword(token.kind))
            dest.append(token.withLocation(alloc, expansionLoc + delta));
        else {
            // check for formal param
            auto it = argumentMap.find(token.valueText());
            if (it == argumentMap.end())
                dest.append(token.withLocation(alloc, expansionLoc + delta));
            else {
                // we need to ensure that we get correct spacing for the leading token here;
                // it needs to come from the *formal* parameter used in the macro body, not
                // from the argument itself
                auto begin = it->second->begin();
                auto end = it->second->end();
                if (begin != end) {
                    dest.append(begin->withTrivia(alloc, token.trivia()));
                    dest.appendRange(++begin, end);
                } else {
                    // the macro argument contained no tokens.
                    // we still need to supply an empty token here to ensure
                    // that the trivia of the formal paremter is passed on
                    dest.append(Token(TokenKind::EmptyMacroArgument, token.getInfo()));
                }
            }
        }
    }

    return true;
}

bool Preprocessor::expandReplacementList(ArrayRef<Token>& tokens) {
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
            if (token.kind != TokenKind::Directive || token.directiveKind() != SyntaxKind::MacroUsage)
                currentBuffer->append(token);
            else {
                // lookup the macro definition
                auto definition = findMacro(token);
                if (!definition)
                    return false;

                // parse arguments if necessary
                MacroActualArgumentListSyntax* actualArgs = nullptr;
                if (definition->formalArguments) {
                    actualArgs = parser.parseActualArgumentList();
                    if (!actualArgs)
                        return false;
                }

                if (!expandMacro(definition, token, actualArgs, *currentBuffer))
                    return false;

                expandedSomething = true;
            }
        }

        // shake the box until the cat stops making noise
        tokens = ArrayRef<Token>(currentBuffer->begin(), currentBuffer->end());
        std::swap(currentBuffer, nextBuffer);
        currentBuffer->clear();

    } while (expandedSomething);

    // Make a heap copy of the tokens before we leave
    tokens = nextBuffer->copy(alloc);
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

        auto kind = peek().kind;
        if (kind == TokenKind::CloseParenthesis)
            break;
        else if (kind == TokenKind::Comma)
            buffer.append(consume());
        else {
            // TODO: skipped tokens
        }
    }
}

MacroActualArgumentSyntax* Preprocessor::MacroParser::parseActualArgument() {
    auto arg = parseTokenList();
    return pp.alloc.emplace<MacroActualArgumentSyntax>(arg);
}

MacroFormalArgumentSyntax* Preprocessor::MacroParser::parseFormalArgument() {
    Token arg = peek();
    if (arg.kind == TokenKind::Identifier || isKeyword(arg.kind)) {
        consume();
    } else {
        arg = expect(TokenKind::Identifier);
    }

    MacroArgumentDefaultSyntax* argDef = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        argDef = pp.alloc.emplace<MacroArgumentDefaultSyntax>(equals, parseTokenList());
    }

    return pp.alloc.emplace<MacroFormalArgumentSyntax>(arg, argDef);
}

ArrayRef<Token> Preprocessor::MacroParser::parseTokenList() {
    // comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}
    // otherwise, keep swallowing tokens as part of the default
    SmallVectorSized<Token, 64> tokens;
    SmallVectorSized<TokenKind, 16> delimPairStack;
    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfDirective) {
            if (delimPairStack.empty())
                pp.addError(DiagCode::ExpectedEndOfMacroArgs, peek().location());
            else
                pp.addError(DiagCode::UnbalancedMacroArgDims, peek().location()) << getTokenKindText(delimPairStack.back());
            delimPairStack.clear();
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

void Preprocessor::MacroParser::setBuffer(ArrayRef<Token> newBuffer) {
    buffer = newBuffer;
    currentIndex = 0;
}

Token Preprocessor::MacroParser::next() {
    if (currentIndex < buffer.count())
        return buffer[currentIndex++];
    return Token();
}

Token Preprocessor::MacroParser::peek() {
    if (currentIndex < buffer.count())
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
    if (currentIndex >= buffer.count())
        return pp.expect(kind, currentMode);

    if (buffer[currentIndex].kind != kind) {
        Token last = currentIndex > 0 ? buffer[currentIndex - 1] : Token();
        return Token::createExpected(pp.alloc, pp.diagnostics, buffer[currentIndex], kind, last);
    }
    return next();
}

}
