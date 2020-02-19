//------------------------------------------------------------------------------
// Preprocessor_macros.cpp
// Macro-related preprocessor support
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace slang {

using LF = LexerFacts;

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
        addDiag(diag::UnknownDirective, directive.location()) << directive.valueText();

        // If we see a parenthesis next, let's assume they tried to invoke a function-like macro
        // and skip over the tokens.
        if (peek(TokenKind::OpenParenthesis))
            return MacroParser(*this).parseActualArgumentList(directive);
        return nullptr;
    }

    // if this assert fires, we failed to fully expand nested macros at a previous point
    ASSERT(!currentMacroToken);

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (macro.needsArgs()) {
        actualArgs = MacroParser(*this).parseActualArgumentList(directive);
        if (!actualArgs)
            return nullptr;
    }

    // Expand out the macro
    SmallVectorSized<Token, 32> buffer;
    MacroExpansion expansion{ sourceManager, alloc, buffer, directive, true };
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
        // Start by recursively expanding out all valid macro usages. We keep track of
        // the token pointer here so that we can detect if expandReplacementList actually
        // did any work; if it did we want to ensure that we come back around for another
        // pass. This ensures that we don't miss expanding a constructed macro.
        const Token* ptr = tokens.data();
        if (!expandReplacementList(tokens, alreadyExpanded))
            return actualArgs;

        // Now that all macros have been expanded, handle token concatenation and stringification.
        expandedTokens.clear();
        if (!applyMacroOps(tokens, expandedTokens) && ptr == tokens.data())
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

    for (size_t i = 0; i < tokens.size(); i++) {
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

                    addDiag(diag::IgnoredMacroPaste, token.location());
                }
                else if (stringify) {
                    // if this is right after the opening quote or right before the closing quote,
                    // we're trying to concatenate something with nothing, so assume an error
                    if (stringifyBuffer.empty() || tokens[i + 1].kind == TokenKind::MacroQuote)
                        addDiag(diag::IgnoredMacroPaste, token.location());
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
                    // Dest cannot be empty here.
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
        // we find. Note that this can be left over at the end of applying ops; that's fine,
        // nothing is relying on observing this after the end of the macro's tokens.
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
        if (newToken.kind == TokenKind::Identifier && !newToken.rawText().empty() &&
            newToken.rawText()[0] == '\\') {

            size_t offset = newToken.rawText().find("`\"");
            if (offset != std::string_view::npos) {
                // Split the token, finish the stringification.
                Token split(alloc, TokenKind::Identifier, newToken.trivia(),
                            newToken.rawText().substr(0, offset), newToken.location());
                stringifyBuffer.append(split);

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

        stringifyBuffer.append(newToken);
    }

    if (stringify)
        addDiag(diag::ExpectedMacroStringifyEnd, stringify.location());

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
        SourceLocation expansionLoc =
            sourceManager.createExpansionLoc(start, expansion.getRange(), macroName);

        // simple macro; just take body tokens
        for (auto token : body)
            expansion.append(token, expansionLoc, start, expansion.getRange());

        return true;
    }

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = directive->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.size() > formalList.size()) {
        addDiag(diag::TooManyActualMacroArgs, actualArgs->getFirstToken().location());
        return false;
    }

    struct ArgTokens : public span<const Token> {
        using span<const Token>::span;
        using span<const Token>::operator=;
        bool isExpanded = false;
    };
    SmallMap<string_view, ArgTokens, 8> argumentMap;

    for (size_t i = 0; i < formalList.size(); i++) {
        auto formal = formalList[i];
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
                addDiag(diag::NotEnoughMacroArgs, actualArgs->closeParen.location());
                return false;
            }
        }

        auto name = formal->name.valueText();
        if (!name.empty())
            argumentMap.emplace(name, ArgTokens(*tokenList));
    }

    Token endOfArgs = actualArgs->getLastToken();
    SourceRange expansionRange(expansion.getRange().start(),
                               endOfArgs.location() + endOfArgs.rawText().length());

    SourceLocation start = body[0].location();
    SourceLocation expansionLoc =
        sourceManager.createExpansionLoc(start, expansionRange, macroName);

    // now add each body token, substituting arguments as necessary
    for (auto& token : body) {
        if (token.kind != TokenKind::Identifier && !LF::isKeyword(token.kind) &&
            (token.kind != TokenKind::Directive ||
             token.directiveKind() != SyntaxKind::MacroUsage)) {

            expansion.append(token, expansionLoc, start, expansionRange);
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
            expansion.append(token, expansionLoc, start, expansionRange);
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
            Token empty(alloc, TokenKind::EmptyMacroArgument, token.trivia(), ""sv,
                        token.location());
            expansion.append(empty, expansionLoc, start, expansionRange);
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
        SourceLocation tokenLoc = expansion.adjustLoc(token, expansionLoc, start, expansionRange);
        SourceRange argRange(tokenLoc, tokenLoc + token.rawText().length());
        SourceLocation argLoc = sourceManager.createExpansionLoc(firstLoc, argRange, true);

        // See note above about weird macro usage being argument replaced.
        // In that case we want to fabricate the correct directive token here.
        if (token.kind == TokenKind::Directive) {
            Token grave(alloc, TokenKind::Directive, first.trivia(), "`"sv, firstLoc,
                        SyntaxKind::Unknown);
            first = Lexer::concatenateTokens(alloc, grave, first);
        }

        expansion.append(first, argLoc, firstLoc, argRange);
        for (++begin; begin != end; begin++)
            expansion.append(*begin, argLoc, firstLoc, argRange);
    }

    return true;
}

SourceRange Preprocessor::MacroExpansion::getRange() const {
    return { usageSite.location(), usageSite.location() + usageSite.rawText().length() };
}

SourceLocation Preprocessor::MacroExpansion::adjustLoc(Token token, SourceLocation& macroLoc,
                                                       SourceLocation& firstLoc,
                                                       SourceRange expansionRange) const {
    // If this token is in the same buffer as the previous one we can keep using the
    // same expansion location; otherwise we need to create a new one that points into
    // the new buffer as its original location.
    if (token.location().buffer() != firstLoc.buffer()) {
        firstLoc = token.location();
        macroLoc = sourceManager.createExpansionLoc(firstLoc, expansionRange, true);
    }

    return macroLoc + (token.location() - firstLoc);
}

void Preprocessor::MacroExpansion::append(Token token, SourceLocation& macroLoc,
                                          SourceLocation& firstLoc, SourceRange expansionRange) {
    SourceLocation location = adjustLoc(token, macroLoc, firstLoc, expansionRange);
    append(token, location);
}

void Preprocessor::MacroExpansion::append(Token token, SourceLocation location) {
    if (!any) {
        if (!isTopLevel)
            token = token.withTrivia(alloc, usageSite.trivia());
        else
            token = token.withTrivia(alloc, {});
        any = true;
    }

    // Line continuations get stripped out when we expand macros and become newline trivia instead.
    if (token.kind == TokenKind::LineContinuation) {
        SmallVectorSized<Trivia, 8> newTrivia;
        newTrivia.appendRange(token.trivia());
        newTrivia.append(Trivia(TriviaKind::EndOfLine, token.rawText().substr(1)));

        dest.append(
            Token(alloc, TokenKind::EmptyMacroArgument, newTrivia.copy(alloc), "", location));
    }
    else {
        dest.append(token.withLocation(alloc, location));
    }
}

bool Preprocessor::expandReplacementList(span<Token const>& tokens,
                                         SmallSet<DefineDirectiveSyntax*, 8>& alreadyExpanded) {
    SmallVectorSized<Token, 64> outBuffer;
    SmallVectorSized<Token, 64> expansionBuffer;

    bool expandedSomething = false;
    MacroParser parser(*this);
    parser.setBuffer(tokens);

    // loop through each token in the replacement list and expand it if it's a nested macro
    Token token;
    while ((token = parser.next())) {
        if (token.kind != TokenKind::Directive || token.directiveKind() != SyntaxKind::MacroUsage) {
            outBuffer.append(token);
            continue;
        }

        // lookup the macro definition
        auto macro = findMacro(token);
        if (!macro.valid()) {
            // If we couldn't find the macro, just keep trucking.
            // It's possible that a future expansion will make this valid.
            outBuffer.append(token);
            continue;
        }

        if (!macro.isIntrinsic() && alreadyExpanded.count(macro.syntax)) {
            addDiag(diag::RecursiveMacro, token.location()) << token.valueText();
            return false;
        }

        // parse arguments if necessary
        MacroActualArgumentListSyntax* actualArgs = nullptr;
        if (macro.needsArgs()) {
            actualArgs = parser.parseActualArgumentList(token);
            if (!actualArgs)
                return false;
        }

        expansionBuffer.clear();
        MacroExpansion expansion{ sourceManager, alloc, expansionBuffer, token, false };
        if (!expandMacro(macro, expansion, actualArgs))
            return false;

        // Recursively expand out nested macros; this ensures that we detect
        // any potentially recursive macros.
        alreadyExpanded.insert(macro.syntax);
        span<const Token> expanded = expansionBuffer;
        if (!expandReplacementList(expanded, alreadyExpanded))
            return false;

        alreadyExpanded.erase(macro.syntax);
        outBuffer.appendRange(expanded);
        expandedSomething = true;
    }

    // Make a heap copy of the tokens before we leave, if we actually expanded something.
    if (expandedSomething)
        tokens = outBuffer.copy(alloc);
    return true;
}

bool Preprocessor::expandIntrinsic(MacroIntrinsic intrinsic, MacroExpansion& expansion) {
    auto loc = expansion.getRange().start();
    SmallVectorSized<char, 64> text;
    switch (intrinsic) {
        case MacroIntrinsic::File: {
            string_view fileName = sourceManager.getFileName(loc);
            text.appendRange(fileName);

            string_view rawText = toStringView(text.copy(alloc));
            Token token(alloc, TokenKind::StringLiteral, {}, rawText, loc, fileName);
            expansion.append(token, loc);
            break;
        }
        case MacroIntrinsic::Line: {
            size_t lineNum = sourceManager.getLineNumber(loc);
            uintToStr(text, lineNum);

            string_view rawText = toStringView(text.copy(alloc));
            Token token(alloc, TokenKind::IntegerLiteral, {}, rawText, loc, lineNum);
            expansion.append(token, loc);
            break;
        }
        case MacroIntrinsic::None:
            THROW_UNREACHABLE;
    }

    return true;
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

MacroActualArgumentListSyntax* Preprocessor::MacroParser::parseActualArgumentList(Token prevToken) {
    // macro has arguments, so we expect to see them here
    if (!peek(TokenKind::OpenParenthesis)) {
        pp.addDiag(diag::ExpectedMacroArgs, prevToken.location() + prevToken.rawText().length());
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
    if (arg.kind == TokenKind::Identifier || LF::isKeyword(arg.kind))
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
                pp.addDiag(diag::UnbalancedMacroArgDims, tokens.back().location())
                    << LF::getTokenKindText(delimPairStack.back());
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

        TokenKind closeKind = SyntaxFacts::getDelimCloseKind(kind);
        if (closeKind != TokenKind::Unknown)
            delimPairStack.append(closeKind);
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
        return Token::createExpected(pp.alloc, pp.diagnostics, buffer[currentIndex], kind, last,
                                     Token());
    }
    return next();
}

static bool isSameToken(Token left, Token right) {
    if (left.kind != right.kind || left.rawText() != right.rawText())
        return false;

    auto lt = left.trivia();
    auto rt = right.trivia();
    if (lt.size() != rt.size())
        return false;

    for (auto lit = lt.begin(), rit = rt.begin(); lit != lt.end(); lit++, rit++) {
        if (lit->kind != rit->kind || lit->getRawText() != rit->getRawText())
            return false;
    }
    return true;
}

static bool isSameTokenList(const TokenList& left, const TokenList& right) {
    if (left.size() != right.size())
        return false;

    for (auto lit = left.begin(), rit = right.begin(); lit != left.end(); lit++, rit++) {
        if (!isSameToken(*lit, *rit))
            return false;
    }
    return true;
}

bool Preprocessor::isSameMacro(const DefineDirectiveSyntax& left,
                               const DefineDirectiveSyntax& right) {
    // Names are assumed to match already.
    if (bool(left.formalArguments) != bool(right.formalArguments))
        return false;

    if (left.formalArguments) {
        auto& la = left.formalArguments->args;
        auto& ra = right.formalArguments->args;
        if (la.size() != ra.size())
            return false;

        for (auto laIt = la.begin(), raIt = ra.begin(); laIt != la.end(); laIt++, raIt++) {
            auto leftArg = *laIt;
            auto rightArg = *raIt;
            if (!isSameToken(leftArg->name, rightArg->name))
                return false;

            if (bool(leftArg->defaultValue) != bool(rightArg->defaultValue))
                return false;

            if (leftArg->defaultValue) {
                if (!isSameTokenList(leftArg->defaultValue->tokens, rightArg->defaultValue->tokens))
                    return false;
            }
        }
    }

    return isSameTokenList(left.body, right.body);
}

} // namespace slang