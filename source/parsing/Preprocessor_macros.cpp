//------------------------------------------------------------------------------
// Preprocessor_macros.cpp
// Macro-related preprocessor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/LexerDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace slang::parsing {

using namespace syntax;

using LF = LexerFacts;

Preprocessor::MacroDef Preprocessor::findMacro(Token directive) {
    std::string_view name = directive.valueText().substr(1);
    if (!name.empty() && name[0] == '\\')
        name = name.substr(1);

    auto it = macros.find(name);
    if (it == macros.end())
        return nullptr;
    return it->second;
}

void Preprocessor::createBuiltInMacro(std::string_view name, int value, std::string_view valueStr) {
#define NL SourceLocation::NoLocation

    if (valueStr.empty()) {
        auto str = std::to_string(value);
        auto ptr = (char*)alloc.allocate(str.length(), 1);
        memcpy(ptr, str.data(), str.length());
        valueStr = std::string_view(ptr, str.length());
    }

    Token directive(alloc, TokenKind::Directive, {}, valueStr, NL, SyntaxKind::DefineDirective);
    Token nameTok(alloc, TokenKind::Identifier, {}, name, NL);

    SmallVector<Token> body;
    body.push_back(Token(alloc, TokenKind::IntegerLiteral, {}, valueStr, NL,
                         SVInt(32, uint64_t(value), true)));

    MacroDef def;
    def.syntax = alloc.emplace<DefineDirectiveSyntax>(directive, nameTok, nullptr,
                                                      body.copy(alloc));
    def.builtIn = true;
    macros[name] = def;

#undef NL
}

std::pair<MacroActualArgumentListSyntax*, Trivia> Preprocessor::handleTopLevelMacro(
    Token directive) {
    auto macro = findMacro(directive);
    if (!macro.valid()) {
        if (options.ignoreDirectives.find(directive.valueText().substr(1)) !=
            options.ignoreDirectives.end()) {
            SmallVector<Token, 4> ignoreTokens;
            while (peekSameLine() && peek().kind != TokenKind::EndOfFile)
                ignoreTokens.push_back(consume());

            if (ignoreTokens.empty())
                return {nullptr, Trivia()};
            else
                return {nullptr, Trivia(TriviaKind::SkippedTokens, ignoreTokens.copy(alloc))};
        }
        addDiag(diag::UnknownDirective, directive.location()) << directive.valueText();

        // If we see a parenthesis next, let's assume they tried to invoke a function-like macro
        // and skip over the tokens.
        if (peek(TokenKind::OpenParenthesis))
            return {MacroParser(*this).parseActualArgumentList(directive), Trivia()};
        return {nullptr, Trivia()};
    }

    // if this assert fires, we failed to fully expand nested macros at a previous point
    SLANG_ASSERT(!currentMacroToken);

    // parse arguments if necessary
    MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (macro.needsArgs()) {
        actualArgs = MacroParser(*this).parseActualArgumentList(directive);
        if (!actualArgs)
            return {nullptr, Trivia()};
    }

    // Expand out the macro
    SmallVector<Token, 32> buffer;
    MacroExpansion expansion{sourceManager, alloc, buffer, directive, true};
    if (!expandMacro(macro, expansion, actualArgs))
        return {actualArgs, Trivia()};

    // The macro is now expanded out into tokens, but some of those tokens might
    // be more macros that need to be expanded, or special characters that
    // perform stringification or concatenation of tokens. It's possible that
    // after concatentation is performed we will have formed new valid macro
    // names that need to be expanded, which is why we loop here.
    SmallSet<const DefineDirectiveSyntax*, 8> alreadyExpanded;
    if (!macro.isIntrinsic())
        alreadyExpanded.insert(macro.syntax);

    std::span<Token const> tokens = buffer.copy(alloc);
    while (true) {
        // Start by recursively expanding out all valid macro usages. We keep track of
        // the token pointer here so that we can detect if expandReplacementList actually
        // did any work; if it did we want to ensure that we come back around for another
        // pass. This ensures that we don't miss expanding a constructed macro.
        const Token* ptr = tokens.data();
        if (!expandReplacementList(tokens, alreadyExpanded))
            return {actualArgs, Trivia()};

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

    return {actualArgs, Trivia()};
}

bool Preprocessor::applyMacroOps(std::span<Token const> tokens, SmallVectorBase<Token>& dest) {
    SmallVector<Trivia, 8> emptyArgTrivia;
    SmallVector<Token, 8> stringifyBuffer;
    SmallVector<Token, 8> commentBuffer;
    Token stringify;
    Token syntheticComment;
    Token extraToAppend;
    bool anyNewMacros = false;
    bool didConcat = false;

    for (size_t i = 0; i < tokens.size(); i++) {
        Token newToken;
        bool nextDidConcat = false;

        // Once we see a `" token, we start collecting tokens into their own
        // buffer for stringification. Otherwise, just add them to the final
        // expansion buffer.
        Token token = tokens[i];
        switch (token.kind) {
            case TokenKind::MacroQuote:
            case TokenKind::MacroTripleQuote:
                if (!stringify) {
                    stringify = token;
                    stringifyBuffer.clear();

                    if (token.kind == TokenKind::MacroTripleQuote &&
                        options.languageVersion < LanguageVersion::v1800_2023) {
                        addDiag(diag::WrongLanguageVersion, token.location())
                            << toString(options.languageVersion);
                    }
                }
                else if (token.kind == stringify.kind) {
                    // all done stringifying; convert saved tokens to string
                    newToken = Lexer::stringify(*lexerStack.back(), stringify, stringifyBuffer,
                                                token);
                    stringify = Token();
                }
                else if (stringify.kind == TokenKind::MacroTripleQuote) {
                    // We found a `" inside of a triple quoted stringification.
                    // Just keep it, let it become part of the string contents.
                    newToken = token;
                }
                else {
                    // We found a `""" inside of a single quoted stringification.
                    // The LRM doesn't say what to do, but I think it makes sense to
                    // split the token, end the previous stringification, and then
                    // append the essentially empty string literal after it.
                    // This will cause an error down the line since two string literals
                    // next to each other isn't ever valid.
                    newToken = Lexer::stringify(*lexerStack.back(), stringify, stringifyBuffer,
                                                token);
                    stringify = Token();
                    extraToAppend = Token(alloc, TokenKind::StringLiteral, {}, "\"\"",
                                          token.location() + 2, ""sv);
                }
                break;
            case TokenKind::MacroPaste:
                // Paste together previous token and next token; a macro paste on either end
                // of the buffer or one that borders whitespace should be ignored.
                // This isn't specified in the standard so I'm just guessing.
                if (i == 0 || i == tokens.size() - 1 || !token.trivia().empty() ||
                    !tokens[i + 1].trivia().empty() || !emptyArgTrivia.empty()) {

                    addDiag(diag::IgnoredMacroPaste, token.location());

                    // We're ignoring this token, but don't lose its trivia or our
                    // spacing can get messed up.
                    emptyArgTrivia.append_range(token.trivia());
                }
                else if (stringify) {
                    // If this is right after the opening quote or right before the closing quote,
                    // we're trying to concatenate something with nothing.
                    if (stringifyBuffer.empty() || tokens[i + 1].kind == TokenKind::MacroQuote ||
                        tokens[i + 1].kind == TokenKind::MacroTripleQuote) {
                        addDiag(diag::IgnoredMacroPaste, token.location());
                    }
                    else {
                        newToken = Lexer::concatenateTokens(alloc, sourceManager,
                                                            stringifyBuffer.back(), tokens[i + 1]);
                        if (newToken) {
                            stringifyBuffer.pop_back();
                            ++i;
                        }
                    }
                }
                else if (syntheticComment) {
                    // Check for a *``/ to end the synthetic comment. Otherwise ignore the paste,
                    // since this is just going to become a comment anyway.
                    if (commentBuffer.back().kind == TokenKind::Star &&
                        tokens[i + 1].kind == TokenKind::Slash) {
                        commentBuffer.push_back(tokens[i + 1]);
                        i++;

                        emptyArgTrivia.append_range(syntheticComment.trivia());
                        emptyArgTrivia.push_back(
                            Lexer::commentify(alloc, sourceManager, commentBuffer));
                        syntheticComment = Token();
                    }
                }
                else {
                    // Dest cannot be empty here, though it's not easy to see why at first glance.
                    Token left = dest.back();
                    Token right = tokens[i + 1];

                    // Other tools allow concatenating a '/' with a '*' to form a block comment.
                    // This seems like utter nonsense but real world code depends on it so
                    // we have to support it as well.
                    if (left.kind == TokenKind::Slash && right.kind == TokenKind::Star) {
                        commentBuffer.clear();
                        syntheticComment = left;
                        dest.pop_back();
                        ++i;

                        commentBuffer.push_back(left.withTrivia(alloc, {}));
                        newToken = right;
                    }
                    else {
                        newToken = Lexer::concatenateTokens(alloc, sourceManager, dest.back(),
                                                            tokens[i + 1]);
                        if (newToken) {
                            dest.pop_back();
                            ++i;

                            nextDidConcat = true;
                            anyNewMacros |= newToken.kind == TokenKind::Directive &&
                                            newToken.directiveKind() == SyntaxKind::MacroUsage;
                        }
                    }
                }
                break;
            default: {
                // If last iteration we did a token concatenation, check whether this token
                // is right next to it (not leading trivia). If so, we should try to
                // continue the concatenation process.
                if (didConcat && token.trivia().empty() && emptyArgTrivia.empty()) {
                    newToken = Lexer::concatenateTokens(alloc, sourceManager, dest.back(), token);
                    if (newToken) {
                        dest.pop_back();
                        nextDidConcat = true;
                        break;
                    }
                }

                // Otherwise take the token as it is.
                newToken = token;
                break;
            }
        }

        didConcat = nextDidConcat;
        if (!newToken)
            continue;

        // If we have an empty macro argument just collect its trivia and use it on the next token
        // we find. Note that this can be left over at the end of applying ops; that's fine,
        // nothing is relying on observing this after the end of the macro's tokens.
        if (newToken.kind == TokenKind::EmptyMacroArgument) {
            emptyArgTrivia.append_range(newToken.trivia());
            continue;
        }

        if (!emptyArgTrivia.empty()) {
            emptyArgTrivia.append_range(newToken.trivia());
            newToken = newToken.withTrivia(alloc, emptyArgTrivia.copy(alloc));
            emptyArgTrivia.clear();
        }

        if (!stringify) {
            if (syntheticComment) {
                commentBuffer.push_back(newToken);
            }
            else {
                dest.push_back(newToken);
                if (extraToAppend) {
                    dest.push_back(extraToAppend);
                    extraToAppend = Token();
                }
            }
            continue;
        }

        // If this is an escaped identifier that includes a `" within it, we need to split the
        // token up to match the behavior of other simulators.
        auto raw = newToken.rawText();
        if (newToken.kind == TokenKind::Identifier && !raw.empty() && raw[0] == '\\') {
            size_t offset = raw.find("`\"");
            if (offset != std::string_view::npos) {
                // Like above, we need to handle the case of mismatched delimiters.
                // If we match, we complete the stringification. If we found a `"
                // inside a triple quoted string, just keep going. If we found a `"""
                // inside a single quoted string, split and end.
                const bool startIsTriple = stringify.kind == TokenKind::MacroTripleQuote;
                const bool endIsTriple = raw.substr(offset).starts_with(R"(`""")");
                if (startIsTriple == endIsTriple || !startIsTriple) {
                    stringifyBuffer.push_back(newToken.withRawText(alloc, raw.substr(0, offset)));

                    // Note: endToken parameter here doesn't matter,
                    // we know there is no trivia to take.
                    dest.push_back(
                        Lexer::stringify(*lexerStack.back(), stringify, stringifyBuffer, Token()));
                    stringify = Token();

                    // Now we have the unfortunate task of re-lexing the remaining stuff after the
                    // split and then appending those tokens to the destination as well.
                    SmallVector<Token, 8> splits;
                    splitTokens(newToken, offset + (endIsTriple ? 4 : 2), splits);
                    anyNewMacros |= applyMacroOps(splits, dest);
                    continue;
                }
            }
        }

        stringifyBuffer.push_back(newToken);
    }

    if (stringify)
        addDiag(diag::ExpectedMacroStringifyEnd, stringify.location());

    return anyNewMacros;
}

bool Preprocessor::expandMacro(MacroDef macro, MacroExpansion& expansion,
                               MacroActualArgumentListSyntax* actualArgs) {
    if (macro.isIntrinsic()) {
        // for now, no intrisics can have arguments
        SLANG_ASSERT(!actualArgs);
        return expandIntrinsic(macro.intrinsic, expansion);
    }

    const DefineDirectiveSyntax* directive = macro.syntax;
    SLANG_ASSERT(directive);

    // ignore empty macro
    const auto& body = directive->body;
    if (body.empty())
        return true;

    std::string_view macroName = directive->name.valueText();

    if (!directive->formalArguments) {
        // each macro expansion gets its own location entry
        SourceLocation start = body[0].location();
        SourceLocation expansionLoc = sourceManager.createExpansionLoc(start, expansion.getRange(),
                                                                       macroName);

        // simple macro; just take body tokens
        for (auto token : body)
            expansion.append(token, expansionLoc, start, expansion.getRange());

        return true;
    }

    // match up actual arguments with formal parameters
    SLANG_ASSERT(actualArgs);
    auto& formalList = directive->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.size() > formalList.size()) {
        addDiag(diag::TooManyActualMacroArgs, actualArgs->getFirstToken().location());
        return false;
    }

    struct ArgTokens : public std::span<const Token> {
        using std::span<const Token>::span;
        using std::span<const Token>::operator=;
        bool isExpanded = false;
    };
    SmallMap<std::string_view, ArgTokens, 8> argumentMap;

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
    SourceLocation expansionLoc = sourceManager.createExpansionLoc(start, expansionRange,
                                                                   macroName);

    auto append = [&](Token token) {
        expansion.append(token, expansionLoc, start, expansionRange);
        return true;
    };

    bool inDefineDirective = false;

    auto handleToken = [&](Token token) {
        if (inDefineDirective && !token.isOnSameLine())
            inDefineDirective = false;

        if (token.kind != TokenKind::Identifier && !LF::isKeyword(token.kind) &&
            token.kind != TokenKind::Directive) {
            // Non-identifier, can't be argument substituted.
            return append(token);
        }

        std::string_view text = token.valueText();
        if (token.kind == TokenKind::Directive && !text.empty()) {
            if (token.directiveKind() != SyntaxKind::MacroUsage) {
                // If this is the start of a `define directive, note that fact because
                // during argument expansion we will insert line continuations.
                if (token.directiveKind() == SyntaxKind::DefineDirective)
                    inDefineDirective = true;
                return append(token);
            }

            // Other tools allow arguments to replace matching directive names, e.g.:
            // `define FOO(bar) `bar
            // `define ONE 1
            // `FOO(ONE)   // expands to 1
            text = text.substr(1);
        }

        // check for formal param
        auto it = argumentMap.find(text);
        if (it == argumentMap.end())
            return append(token);

        // Fully expand out arguments before substitution to make sure we can detect whether
        // a usage of a macro in a replacement list is valid or an illegal recursion.
        if (!it->second.isExpanded) {
            std::span<const Token> argTokens = it->second;
            SmallSet<const DefineDirectiveSyntax*, 8> alreadyExpanded;
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
            return append(empty);
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
            Token grave(alloc, TokenKind::Unknown, first.trivia(), "`"sv, firstLoc);
            Token combined = Lexer::concatenateTokens(alloc, sourceManager, grave, first);
            if (combined) {
                first = combined;
            }
            else {
                // Failed to combine, so ignore the grave and issue an error.
                addDiag(diag::MisplacedDirectiveChar, firstLoc);
            }
        }

        if (inDefineDirective) {
            // Inside a define directive we need to insert line continuations
            // any time an expanded token will end up on a new line.
            auto appendBody = [&](Token token) {
                if (!token.isOnSameLine()) {
                    Token lc(alloc, TokenKind::LineContinuation, token.trivia(), "\\"sv,
                             token.location());
                    expansion.append(lc, argLoc, firstLoc, argRange,
                                     /* allowLineContinuation */ true);

                    token = token.withTrivia(alloc, {});
                }
                expansion.append(token, argLoc, firstLoc, argRange);
            };

            appendBody(first);
            for (++begin; begin != end; begin++)
                appendBody(*begin);
        }
        else {
            expansion.append(first, argLoc, firstLoc, argRange);
            for (++begin; begin != end; begin++)
                expansion.append(*begin, argLoc, firstLoc, argRange);
        }

        return true;
    };

    // Now add each body token, substituting arguments as necessary.
    for (auto token : body) {
        if (token.kind == TokenKind::Identifier && !token.rawText().empty() &&
            token.rawText()[0] == '\\') {
            // Escaped identifier, might need to break apart and substitute
            // individual pieces of it.
            size_t index = token.rawText().find("``");
            if (index != std::string_view::npos) {
                Token first = token.withRawText(alloc, token.rawText().substr(0, index));
                if (!handleToken(first))
                    return false;

                SmallVector<Token, 8> splits;
                splitTokens(token, index, splits);
                for (auto t : splits) {
                    if (!handleToken(t))
                        return false;
                }

                // Add an empty argument in here so we can make sure a space ends
                // the escaped identifier once it gets concatenated again.
                if (!splits.empty()) {
                    SmallVector<Trivia> triviaBuf;
                    triviaBuf.emplace_back(TriviaKind::Whitespace, " "sv);

                    auto loc = splits.back().location() + splits.back().rawText().length();
                    Token empty(alloc, TokenKind::EmptyMacroArgument, triviaBuf.copy(alloc), ""sv,
                                loc);

                    if (!handleToken(empty))
                        return false;
                }

                continue;
            }
        }

        if (!handleToken(token))
            return false;
    }

    return true;
}

SourceRange Preprocessor::MacroExpansion::getRange() const {
    return {usageSite.location(), usageSite.location() + usageSite.rawText().length()};
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
                                          SourceLocation& firstLoc, SourceRange expansionRange,
                                          bool allowLineContinuation) {
    SourceLocation location = adjustLoc(token, macroLoc, firstLoc, expansionRange);
    append(token, location, allowLineContinuation);
}

void Preprocessor::MacroExpansion::append(Token token, SourceLocation location,
                                          bool allowLineContinuation) {
    if (!any) {
        if (!isTopLevel)
            token = token.withTrivia(alloc, usageSite.trivia());
        else
            token = token.withTrivia(alloc, {});
        any = true;
    }

    // Line continuations get stripped out when we expand macros and become newline trivia instead.
    if (token.kind == TokenKind::LineContinuation && !allowLineContinuation) {
        SmallVector<Trivia, 8> newTrivia;
        newTrivia.append_range(token.trivia());
        newTrivia.push_back(Trivia(TriviaKind::EndOfLine, token.rawText().substr(1)));

        dest.push_back(
            Token(alloc, TokenKind::EmptyMacroArgument, newTrivia.copy(alloc), "", location));
    }
    else {
        dest.push_back(token.withLocation(alloc, location));
    }
}

bool Preprocessor::expandReplacementList(
    std::span<Token const>& tokens, SmallSet<const DefineDirectiveSyntax*, 8>& alreadyExpanded) {

    SmallVector<Token, 16> outBuffer;
    SmallVector<Token, 16> expansionBuffer;

    bool expandedSomething = false;
    MacroParser parser(*this);
    parser.setBuffer(tokens);

    // loop through each token in the replacement list and expand it if it's a nested macro
    Token token;
    while ((token = parser.next())) {
        if (token.kind != TokenKind::Directive || token.directiveKind() != SyntaxKind::MacroUsage) {
            outBuffer.push_back(token);
            continue;
        }

        // lookup the macro definition
        auto macro = findMacro(token);
        if (!macro.valid()) {
            // If we couldn't find the macro, just keep trucking.
            // It's possible that a future expansion will make this valid.
            outBuffer.push_back(token);
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
        MacroExpansion expansion{sourceManager, alloc, expansionBuffer, token, false};
        if (!expandMacro(macro, expansion, actualArgs))
            return false;

        // Recursively expand out nested macros; this ensures that we detect
        // any potentially recursive macros.
        alreadyExpanded.insert(macro.syntax);
        std::span<const Token> expanded = expansionBuffer;
        if (!expandReplacementList(expanded, alreadyExpanded))
            return false;

        alreadyExpanded.erase(macro.syntax);
        outBuffer.append_range(expanded);
        expandedSomething = true;
    }

    // Make a heap copy of the tokens before we leave, if we actually expanded something.
    if (expandedSomething)
        tokens = outBuffer.copy(alloc);
    return true;
}

bool Preprocessor::expandIntrinsic(MacroIntrinsic intrinsic, MacroExpansion& expansion) {
    auto loc = expansion.getRange().start();
    SmallVector<char> text;
    switch (intrinsic) {
        case MacroIntrinsic::File: {
            std::string_view fileName = sourceManager.getFileName(loc);
            text.push_back('"');
            text.append_range(fileName);
            text.push_back('"');

            std::string_view rawText = toStringView(text.copy(alloc));
            Token token(alloc, TokenKind::StringLiteral, {}, rawText, loc, fileName);
            expansion.append(token, loc);
            break;
        }
        case MacroIntrinsic::Line: {
            size_t lineNum = sourceManager.getLineNumber(loc);
            uintToStr(text, static_cast<uint64_t>(lineNum));

            std::string_view rawText = toStringView(text.copy(alloc));
            Token token(alloc, TokenKind::IntegerLiteral, {}, rawText, loc, lineNum);
            expansion.append(token, loc);
            break;
        }
        case MacroIntrinsic::None:
            SLANG_UNREACHABLE;
    }

    return true;
}

bool Preprocessor::MacroDef::needsArgs() const {
    return syntax && syntax->formalArguments;
}

MacroFormalArgumentListSyntax* Preprocessor::MacroParser::parseFormalArgumentList() {
    auto openParen = consume();

    Token closeParen;
    SmallVector<TokenOrSyntax, 8> arguments;
    parseArgumentList(arguments, [this]() { return parseFormalArgument(); }, closeParen);

    return pp.alloc.emplace<MacroFormalArgumentListSyntax>(openParen, arguments.copy(pp.alloc),
                                                           closeParen);
}

MacroActualArgumentListSyntax* Preprocessor::MacroParser::parseActualArgumentList(Token prevToken) {
    // macro has arguments, so we expect to see them here
    if (!peek(TokenKind::OpenParenthesis)) {
        pp.addDiag(diag::ExpectedMacroArgs, prevToken.location() + prevToken.rawText().length());
        return nullptr;
    }

    auto openParen = consume();
    Token closeParen;
    SmallVector<TokenOrSyntax, 8> arguments;
    parseArgumentList(arguments, [this]() { return parseActualArgument(); }, closeParen);

    return pp.alloc.emplace<MacroActualArgumentListSyntax>(openParen, arguments.copy(pp.alloc),
                                                           closeParen);
}

template<typename TFunc>
void Preprocessor::MacroParser::parseArgumentList(SmallVectorBase<TokenOrSyntax>& results,
                                                  TFunc&& parseItem, Token& closeParen) {
    while (true) {
        results.push_back(parseItem());

        if (peek().kind == TokenKind::Comma)
            results.push_back(consume());
        else
            break;
    }

    closeParen = expect(TokenKind::CloseParenthesis);
}

MacroActualArgumentSyntax* Preprocessor::MacroParser::parseActualArgument() {
    return pp.alloc.emplace<MacroActualArgumentSyntax>(parseTokenList(true));
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

std::span<Token> Preprocessor::MacroParser::parseTokenList(bool allowNewlines) {
    SmallVector<Token, 16> tokens;
    SmallVector<TokenKind> delimPairStack;

    // Comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}, otherwise, keep swallowing
    // tokens as part of the list.
    while (true) {
        auto kind = peek().kind;
        if (kind == TokenKind::EndOfFile || (!allowNewlines && !peek().isOnSameLine())) {
            if (!delimPairStack.empty()) {
                pp.addDiag(diag::UnbalancedMacroArgDims, tokens.back().location())
                    << LF::getTokenKindText(delimPairStack.back());
            }
            break;
        }

        if (delimPairStack.empty()) {
            if (kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis)
                break;
        }
        else if (delimPairStack.back() == kind) {
            delimPairStack.pop_back();
        }

        tokens.push_back(consume());

        TokenKind closeKind = SyntaxFacts::getDelimCloseKind(kind);
        if (closeKind != TokenKind::Unknown)
            delimPairStack.push_back(closeKind);
    }
    return tokens.copy(pp.alloc);
}

void Preprocessor::MacroParser::setBuffer(std::span<Token const> newBuffer) {
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

void Preprocessor::splitTokens(Token sourceToken, size_t offset, SmallVectorBase<Token>& results) {
    Lexer::splitTokens(alloc, diagnostics, sourceManager, sourceToken, offset,
                       getCurrentKeywordVersion(), results);
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

} // namespace slang::parsing
