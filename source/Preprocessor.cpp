#include "Preprocessor.h"

#include "AllSyntax.h"
#include "BumpAllocator.h"
#include "SourceManager.h"

namespace slang {

SyntaxKind getDirectiveKind(StringRef directive);

Preprocessor::Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceManager(sourceManager),
    alloc(alloc),
    diagnostics(diagnostics)
{
    keywordTable = getKeywordTable();
}

void Preprocessor::pushSource(StringRef source) {
    auto buffer = sourceManager.assignText(source);
    pushSource(buffer);
}

void Preprocessor::pushSource(const SourceBuffer* buffer) {
    ASSERT(lexerStack.size() < MaxIncludeDepth);
    auto lexer = alloc.emplace<Lexer>(buffer, alloc, diagnostics);
    lexerStack.push_back(lexer);
}

FileID Preprocessor::getCurrentFile() {
    if (lexerStack.empty())
        return FileID();
    return lexerStack.back()->getFile();
}

Token* Preprocessor::next() {
    return next(LexerMode::Normal);
}

Token* Preprocessor::next(LexerMode mode) {
    // common case: lex a token and return it
    auto token = nextRaw(mode);
    if (token->kind != TokenKind::Directive || inMacroBody)
        return token;

    // burn through any preprocessor directives we find and convert them to trivia
    auto trivia = triviaPool.get();
    do {
        // TODO: handle all directive types
        // TODO: check keyword eligibility
        switch (token->directiveKind()) {
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
            case SyntaxKind::UndefineAllDirective:
            case SyntaxKind::UnconnectedDriveDirective:
            case SyntaxKind::NoUnconnectedDriveDirective:
            case SyntaxKind::CellDefineDirective:
            case SyntaxKind::EndCellDefineDirective:
            default:
                trivia.append(createSimpleDirective(token));
                break;
        }
        token = nextRaw(mode);
    } while (token->kind == TokenKind::Directive);

    trivia.appendRange(token->trivia);
    token->trivia = trivia.copy(alloc);
    return token;
}

Token* Preprocessor::nextRaw(LexerMode mode) {
    // it's possible we have a token buffered from looking ahead when handling a directive
    if (currentToken) {
        auto result = currentToken;
        currentToken = nullptr;
        return result;
    }

    // if we just expanded a macro we'll have tokens from that to return
    if (currentMacroToken) {
        auto result = *currentMacroToken;
        currentMacroToken++;
        if (currentMacroToken == expandedTokens.end())
            currentMacroToken = nullptr;

        return result;
    }

    // if this assert fires, the user disregarded an EoF and kept calling next()
    ASSERT(!lexerStack.empty());

    // Pull the next token from the active source.
    // This is the common case.
    auto& source = lexerStack.back();
    auto token = source->lex(mode);
    if (token->kind != TokenKind::EndOfFile) {
        // The idea here is that if we have more things on the stack,
        // the current lexer must be for an include file
        if (lexerStack.size() > 1)
            token->markAsPreprocessed();
        return token;
    }

    // don't return EndOfFile tokens for included files, fall
    // through to loop to merge trivia
    lexerStack.pop_back();
    if (lexerStack.empty())
        return token;

    // Rare case: we have an EoF from an include file... we don't want to return
    // that one, but we do want to merge its trivia with whatever comes next.
    auto trivia = triviaPool.get();
    trivia.appendRange(token->trivia);

    while (true) {
        auto& nextSource = lexerStack.back();
        token = nextSource->lex(mode);
        trivia.appendRange(token->trivia);
        if (token->kind != TokenKind::EndOfFile)
            break;

        lexerStack.pop_back();
        if (lexerStack.empty())
            break;
    }

    // finally found a real token to return, so update trivia and get out of here
    token->trivia = trivia.copy(alloc);
    if (lexerStack.size() > 1)
        token->markAsPreprocessed();
    return token;
}

Trivia Preprocessor::handleIncludeDirective(Token* directive) {
    // next token should be a filename
    // TODO: handle macro replaced include file name
    Token* fileName = next(LexerMode::IncludeFileName);
    Token* end = parseEndOfDirective();

    StringRef path = fileName->valueText();
    if (path.length() < 3)
        addError(DiagCode::ExpectedIncludeFileName);
    else {
        // remove delimiters
        path = path.subString(1, path.length() - 2);
        SourceBuffer* buffer = sourceManager.readHeader(path, getCurrentFile(), false);
        if (!buffer)
            addError(DiagCode::CouldNotOpenIncludeFile, fileName->location);
        else if (lexerStack.size() >= MaxIncludeDepth)
            addError(DiagCode::ExceededMaxIncludeDepth);
        else
            pushSource(buffer);
    }

    auto syntax = alloc.emplace<IncludeDirectiveSyntax>(directive, fileName, end);
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleResetAllDirective(Token* directive) {
    // TODO: reset all preprocessor state here
    return createSimpleDirective(directive);
}

Trivia Preprocessor::handleDefineDirective(Token* directive) {
    MacroFormalArgumentListSyntax* formalArguments = nullptr;
    bool noErrors = false;

    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    if (!name->isMissing()) {
        if (getDirectiveKind(name->valueText()) != SyntaxKind::MacroUsage)
            addError(DiagCode::InvalidMacroName, name->location);
        else {
            // check if this is a function-like macro, which requires an opening paren with no leading space
            if (peek(TokenKind::OpenParenthesis) && peek()->trivia.empty()) {
                MacroParser parser(*this);
                formalArguments = parser.parseFormalArgumentList();
            }
            noErrors = true;
        }
    }

    // consume all remaining tokens as macro text
    auto body = tokenPool.get();
    inMacroBody = true;
    while (!peek(TokenKind::EndOfDirective))
        body.append(consume());
    inMacroBody = false;

    auto result = alloc.emplace<DefineDirectiveSyntax>(
        directive,
        name,
        formalArguments,
        body.copy(alloc),
        consume()
    );

    if (noErrors)
        macros[name->valueText().intern(alloc)] = result;
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleMacroUsage(Token* directive) {
    // TODO: don't call createsimpledirective in here

    // lookup the macro definition
    auto definition = findMacro(directive);
    if (!definition) {
        // TODO:
    }

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (definition->formalArguments) {
        MacroParser parser(*this);
        actualArgs = parser.parseActualArgumentList();
        if (!actualArgs) {
            // TODO:
        }
    }

    expandMacro(definition, actualArgs, dest);
    expandReplacementList(dest, finalTokens);

    // TODO: concatenate, stringize, etc
    
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleIfDefDirective(Token* directive, bool not) {
    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    bool take = false;
    if (branchStack.empty() || branchStack.back().currentActive) {
        take = macros.find(name->valueText()) != macros.end();
        if (not)
            take = !take;
    }

    branchStack.push_back(BranchEntry(take));

    return parseBranchDirective(directive, name, take);
}

Trivia Preprocessor::handleElsIfDirective(Token* directive) {
    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);
    bool take = shouldTakeElseBranch(directive->location, true, name->valueText());
    return parseBranchDirective(directive, name, take);
}

Trivia Preprocessor::handleElseDirective(Token* directive) {
    bool take = shouldTakeElseBranch(directive->location, false, nullptr);
    return parseBranchDirective(directive, nullptr, take);
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

Trivia Preprocessor::parseBranchDirective(Token* directive, Token* condition, bool taken) {
    auto eod = parseEndOfDirective();

    // skip over everything until we find another conditional compilation directive
    auto skipped = tokenPool.get();
    if (!taken) {
        while (true) {
            auto token = nextRaw(LexerMode::Normal);

            // EoF or conditional directive stops the skipping process
            bool done = false;
            if (token->kind == TokenKind::EndOfFile)
                done = true;
            else if (token->kind == TokenKind::Directive) {
                switch (token->directiveKind()) {
                    // we still need to handle line continuations correctly for macro defines
                    case SyntaxKind::DefineDirective:
                        do {
                            skipped.append(token);
                            token = nextRaw(LexerMode::Directive);
                        } while (token->kind != TokenKind::EndOfDirective);
                        break;

                    case SyntaxKind::IfDefDirective:
                    case SyntaxKind::IfNDefDirective:
                    case SyntaxKind::ElsIfDirective:
                    case SyntaxKind::ElseDirective:
                    case SyntaxKind::EndIfDirective:
                        done = true;
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
            directive->directiveKind(),
            directive,
            condition,
            eod,
            skipped.copy(alloc)
        );
    }
    else {
        syntax = alloc.emplace<UnconditionalBranchDirectiveSyntax>(
            directive->directiveKind(),
            directive,
            eod,
            skipped.copy(alloc)
        );
    }
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleEndIfDirective(Token* directive) {
    // pop the active branch off the stack
    bool taken = true;
    if (branchStack.empty())
        addError(DiagCode::UnexpectedConditionalDirective, directive->location);
    else {
        branchStack.pop_back();
        if (!branchStack.empty() && !branchStack.back().currentActive)
            taken = false;
    }
    return parseBranchDirective(directive, nullptr, taken);
}

void Preprocessor::expectTimescaleSpecifier(Token*& value, Token*& unit) {
    // TODO: check for allowed values
    auto token = peek();
    if (token->kind == TokenKind::IntegerLiteral) {
        value = consume();
        unit = expect(TokenKind::Identifier);
    }
    else if (token->kind == TokenKind::TimeLiteral) {
        // TODO: split the token
        value = consume();
        unit = nullptr;
    }
    else {
        value = nullptr;
        unit = nullptr;
    }
}

Trivia Preprocessor::handleTimescaleDirective(Token* directive) {
    // TODO: error checking
    Token *value, *valueUnit, *precision, *precisionUnit;
    expectTimescaleSpecifier(value, valueUnit);

    auto slash = expect(TokenKind::Slash);
    expectTimescaleSpecifier(precision, precisionUnit);

    auto eod = parseEndOfDirective();
    auto timescale = alloc.emplace<TimescaleDirectiveSyntax>(directive, value, valueUnit, slash, precision, precisionUnit, eod);
    return Trivia(TriviaKind::Directive, timescale);
}

Trivia Preprocessor::handleDefaultNetTypeDirective(Token* directive) {
    Token* netType = nullptr;
    switch (peek()->kind) {
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
            if (peek()->rawText() == "none")
                netType = consume();
            break;
        default:
            break;
    }

    if (!netType) {
        addError(DiagCode::ExpectedNetType, peek()->location);
        netType = Token::missing(alloc, TokenKind::WireKeyword, peek()->location);
    }

    auto result = alloc.emplace<DefaultNetTypeDirectiveSyntax>(directive, netType, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, result);
}

Token* Preprocessor::parseEndOfDirective(bool suppressError) {
    // consume all extraneous tokens as SkippedToken trivia
    auto skipped = tokenPool.get();
    if (!peek(TokenKind::EndOfDirective)) {
        if (!suppressError)
            addError(DiagCode::ExpectedEndOfDirective, peek()->location);
        do {
            skipped.append(consume());
        } while (!peek(TokenKind::EndOfDirective));
    }

    Token* eod = consume();
    if (!skipped.empty()) {
        // splice together the trivia
        auto trivia = triviaPool.get();
        trivia.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
        trivia.appendRange(eod->trivia);
        eod->trivia = trivia.copy(alloc);
    }

    return eod;
}

Trivia Preprocessor::createSimpleDirective(Token* directive, bool suppressError) {
    DirectiveSyntax* syntax = alloc.emplace<SimpleDirectiveSyntax>(directive->directiveKind(), directive, parseEndOfDirective(suppressError));
    return Trivia(TriviaKind::Directive, syntax);
}

DefineDirectiveSyntax* Preprocessor::findMacro(Token* directive) {
    auto it = macros.find(directive->valueText().subString(1));
    if (it == macros.end()) {
        addError(DiagCode::UnknownDirective, directive->location);
        return nullptr;
    }
    return it->second;
}

void Preprocessor::expandMacro(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs, Buffer<Token*>& dest) {
    if (!macro->formalArguments) {
        // simple macro; just take body tokens
        dest.appendRange(macro->body);
        return;
    }

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = macro->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.count() > formalList.count()) {
        // TODO: error
    }

    argumentMap.clear();
    for (uint32_t i = 0; i < formalList.count(); i++) {
        auto formal = formalList[i];
        auto name = formal->name->valueText();

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
                // TODO: error
                return;
            }
        }

        // fully expand the argument's tokens before substitution
        // TODO:
        //if (!expandReplacementList(tokenList))
        //    return;

        argumentMap[name] = tokenList;
    }

    // now add each body token, substituting arguments as necessary
    for (auto& token : macro->body) {
        if (token->kind != TokenKind::Identifier)
            expandedTokens.append(token);
        else {
            // check for formal param
            auto it = argumentMap.find(token->valueText());
            if (it == argumentMap.end())
                dest.append(token);
            else
                dest.appendRange(*it->second);
        }
    }
}

void Preprocessor::expandReplacementList(ArrayRef<Token*> tokens, Buffer<Token*>& dest) {
    MacroParser parser(*this);
    parser.setBuffer(tokens);

    // loop through each token in the replacement list and expand it if it's a nested macro
    Token* token;
    while ((token = parser.next()) != nullptr) {
        if (token->kind != TokenKind::Directive || token->directiveKind() != SyntaxKind::MacroUsage)
            dest.append(token);
        else {
            // lookup the macro definition
            auto definition = findMacro(token);
            if (!definition) {
                // TODO:
            }

            // parse arguments if necessary
            MacroActualArgumentListSyntax* actualArgs = nullptr;
            if (definition->formalArguments) {
                actualArgs = parser.parseActualArgumentList();
                if (!actualArgs) {
                    // TODO:
                }
            }

            expandMacro(definition, actualArgs, dest);
        }
    }
}

Token* Preprocessor::peek(LexerMode mode) {
    if (!currentToken)
        currentToken = next(mode);
    return currentToken;
}

Token* Preprocessor::consume(LexerMode mode) {
    auto result = peek(mode);
    currentToken = nullptr;
    return result;
}

Token* Preprocessor::expect(TokenKind kind, LexerMode mode) {
    auto result = peek(mode);
    if (result->kind != kind) {
        // report an error here for the missing token
        addError(DiagCode::SyntaxError);
        return Token::missing(alloc, kind, result->location);
    }

    currentToken = nullptr;
    return result;
}

void Preprocessor::addError(DiagCode code) {
    // TODO: location
    diagnostics.emplace(code, SourceLocation());
}

void Preprocessor::addError(DiagCode code, SourceLocation location) {
    // TODO: location
    diagnostics.emplace(code, location);
}

MacroFormalArgumentListSyntax* Preprocessor::MacroParser::parseFormalArgumentList() {
    // parse all formal arguments
    currentMode = LexerMode::Directive;
    auto openParen = consume();
    auto arguments = pp.syntaxPool.get();
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
        pp.addError(DiagCode::ExpectedMacroArgs);
        return nullptr;
    }

    auto openParen = consume();
    auto arguments = pp.syntaxPool.get();
    parseArgumentList(arguments, [this]() { return parseActualArgument(); });

    auto closeParen = expect(TokenKind::CloseParenthesis);
    return pp.alloc.emplace<MacroActualArgumentListSyntax>(openParen, arguments.copy(pp.alloc), closeParen);
}

template<typename TFunc>
void Preprocessor::MacroParser::parseArgumentList(Buffer<TokenOrSyntax>& buffer, TFunc&& parseItem) {
    while (true) {
        buffer.append(parseItem());

        auto kind = peek()->kind;
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
    auto arg = expect(TokenKind::Identifier);

    MacroArgumentDefaultSyntax* argDef = nullptr;
    if (peek(TokenKind::Equals)) {
        auto equals = consume();
        argDef = pp.alloc.emplace<MacroArgumentDefaultSyntax>(equals, parseTokenList());
    }

    return pp.alloc.emplace<MacroFormalArgumentSyntax>(arg, argDef);
}

ArrayRef<Token*> Preprocessor::MacroParser::parseTokenList() {
    auto tokens = pp.tokenPool.get();

    // comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}
    // otherwise, keep swallowing tokens as part of the default
    while (true) {
        auto kind = peek()->kind;
        if (kind == TokenKind::EndOfDirective) {
            if (pp.delimPairStack.empty())
                pp.addError(DiagCode::ExpectedEndOfMacroArgs);
            else
                pp.addError(DiagCode::UnbalancedMacroArgDims);
            pp.delimPairStack.clear();
            break;
        }

        if (pp.delimPairStack.empty()) {
            if ((kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis))
                break;
        }
        else if (pp.delimPairStack.back() == kind)
            pp.delimPairStack.pop();

        tokens.append(consume());
        switch (kind) {
            case TokenKind::OpenParenthesis:
                pp.delimPairStack.append(TokenKind::CloseParenthesis);
                break;
            case TokenKind::OpenBrace:
                pp.delimPairStack.append(TokenKind::CloseBrace);
                break;
            case TokenKind::OpenBracket:
                pp.delimPairStack.append(TokenKind::CloseBracket);
                break;
        }
    }
    return tokens.copy(pp.alloc);
}

}