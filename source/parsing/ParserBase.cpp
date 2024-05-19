//------------------------------------------------------------------------------
// ParserBase.cpp
// Base class for parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/ParserBase.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Preprocessor.h"

namespace slang::parsing {

using namespace syntax;

using SF = SyntaxFacts;

ParserBase::ParserBase(Preprocessor& preprocessor) :
    alloc(preprocessor.getAllocator()), window(preprocessor) {
}

void ParserBase::prependSkippedTokens(Token& token) {
    SmallVector<Trivia, 8> buffer;
    buffer.push_back(Trivia{TriviaKind::SkippedTokens, skippedTokens.copy(alloc)});
    buffer.append_range(token.trivia());

    token = token.withTrivia(alloc, buffer.copy(alloc));
    skippedTokens.clear();
}

Diagnostics& ParserBase::getDiagnostics() {
    return window.tokenSource.getDiagnostics();
}

Diagnostic& ParserBase::addDiag(DiagCode code, SourceLocation location) {
    // If we issued this error in response to seeing an EOF token, back up and put
    // the error on the last consumed token instead.
    if (peek(TokenKind::EndOfFile) && peek().location() == location) {
        Token last = getLastConsumed();
        if (last)
            location = last.location() + last.rawText().size();
    }

    return getDiagnostics().add(code, location);
}

Diagnostic& ParserBase::addDiag(DiagCode code, SourceRange range) {
    return addDiag(code, range.start()) << range;
}

Token ParserBase::peek(uint32_t offset) {
    while (window.currentOffset + offset >= window.count)
        window.addNew();
    return window.buffer[window.currentOffset + offset];
}

Token ParserBase::peek() {
    if (!window.currentToken) {
        if (window.currentOffset >= window.count)
            window.addNew();
        window.currentToken = window.buffer[window.currentOffset];
    }
    SLANG_ASSERT(window.currentToken);
    return window.currentToken;
}

bool ParserBase::peek(TokenKind kind) {
    return peek().kind == kind;
}

Token ParserBase::consume() {
    auto result = peek();
    window.moveToNext();
    if (!skippedTokens.empty())
        prependSkippedTokens(result);

    if (SF::isOpenDelimOrKeyword(result.kind))
        openDelims.push_back(result);
    else if (SF::isCloseDelimOrKeyword(result.kind) && !openDelims.empty()) {
        lastPoppedDelims = {openDelims.back(), result};
        openDelims.pop_back();
    }

    return result;
}

Token ParserBase::consumeIf(TokenKind kind) {
    if (peek(kind))
        return consume();
    return Token();
}

Token ParserBase::expect(TokenKind kind) {
    if (peek(kind))
        return consume();

    // If this needs to be an end delimiter, see if we know the
    // corresponding open delimiter and if so use that to produce
    // a better error.
    Token matchingDelim;
    if (SF::isCloseDelimOrKeyword(kind) && !openDelims.empty()) {
        if (SF::isMatchingDelims(openDelims.back().kind, kind)) {
            matchingDelim = openDelims.back();
            openDelims.pop_back();
        }
        else {
            // If we hit this point assume that our stack of delims has
            // become unbalanced and flush it.
            openDelims.clear();
        }
        lastPoppedDelims = {};
    }

    Token result = Token::createExpected(alloc, getDiagnostics(), peek(), kind, window.lastConsumed,
                                         matchingDelim);
    return result;
}

void ParserBase::skipToken(std::optional<DiagCode> diagCode) {
    auto token = peek();
    SLANG_ASSERT(token.kind != TokenKind::EndOfFile);

    bool haveDiag = haveDiagAtCurrentLoc();
    skippedTokens.push_back(token);
    window.moveToNext();

    if (diagCode && !haveDiag)
        addDiag(*diagCode, token.range());

    // If the token we're skipping is an opening paren / bracket / brace,
    // skip everything up to the corresponding closing token, otherwise we're
    // pretty much guaranteed to report a bunch of spurious errors inside it.
    TokenKind skipKind = SF::getSkipToKind(token.kind);
    if (skipKind == TokenKind::Unknown)
        return;

    SmallVector<TokenKind> delimStack;
    while (true) {
        token = peek();
        if (token.kind == TokenKind::EndOfFile)
            return;

        // If this is an end keyword but not the one we're looking for,
        // it probably matches something higher in our stack so don't
        // necessarily consume it.
        if (SF::isEndKeyword(token.kind)) {
            while (token.kind != skipKind) {
                if (delimStack.empty())
                    return;

                skipKind = delimStack.back();
                delimStack.pop_back();
            }
        }

        skippedTokens.push_back(token);
        window.moveToNext();

        if (token.kind == skipKind) {
            if (delimStack.empty())
                return;

            skipKind = delimStack.back();
            delimStack.pop_back();
        }
        else {
            TokenKind newSkipKind = SF::getSkipToKind(token.kind);
            if (newSkipKind != TokenKind::Unknown) {
                delimStack.push_back(skipKind);
                skipKind = newSkipKind;
            }
        }
    }
}

void ParserBase::pushTokens(std::span<const Token> tokens) {
    window.insertHead(tokens);
}

Token ParserBase::missingToken(TokenKind kind, SourceLocation location) {
    return Token::createMissing(alloc, kind, location);
}

Token ParserBase::placeholderToken() {
    return Token(alloc, TokenKind::Placeholder, {}, {}, peek().location());
}

Token ParserBase::getLastConsumed() const {
    return window.lastConsumed;
}

SourceLocation ParserBase::getLastLocation() {
    if (window.lastConsumed)
        return window.lastConsumed.location() + window.lastConsumed.rawText().length();

    return peek().location();
}

bool ParserBase::haveDiagAtCurrentLoc() {
    Diagnostics& diags = getDiagnostics();
    auto location = getLastLocation();
    return !diags.empty() && diags.back().isError() &&
           (diags.back().location == location || diags.back().location == peek().location());
}

void ParserBase::reportMissingList(Token current, TokenKind closeKind, Token& closeToken,
                                   DiagCode code) {
    if (!haveDiagAtCurrentLoc())
        addDiag(code, getLastLocation());

    closeToken = missingToken(closeKind, current.location());
}

void ParserBase::reportMisplacedSeparator() {
    auto& diag = addDiag(diag::MisplacedTrailingSeparator, window.lastConsumed.location());
    diag << LexerFacts::getTokenKindText(window.lastConsumed.kind);
}

void ParserBase::Window::addNew() {
    if (count >= capacity) {
        // shift tokens to the left if we are too far to the right
        size_t shift = count - currentOffset;
        if (currentOffset > (capacity >> 1)) {
            if (shift > 0)
                memmove(buffer, buffer + currentOffset, shift * sizeof(Token));
        }
        else {
            capacity *= 2;
            Token* newBuffer = new Token[capacity];
            memcpy(newBuffer, buffer + currentOffset, shift * sizeof(Token));

            delete[] buffer;
            buffer = newBuffer;
        }

        count -= currentOffset;
        currentOffset = 0;
    }

    buffer[count] = tokenSource.next();
    count++;
}

void ParserBase::Window::moveToNext() {
    lastConsumed = currentToken;
    currentToken = Token();
    currentOffset++;
}

void ParserBase::Window::insertHead(std::span<const Token> tokens) {
    if (currentOffset >= tokens.size()) {
        currentOffset -= tokens.size();
        memcpy(buffer + currentOffset, tokens.data(), tokens.size() * sizeof(Token));
        return;
    }

    size_t existing = count - currentOffset;
    SLANG_ASSERT(tokens.size() + existing < capacity);

    memmove(buffer + tokens.size(), buffer + currentOffset, existing * sizeof(Token));
    memcpy(buffer, tokens.data(), tokens.size() * sizeof(Token));

    currentOffset = 0;
    count = tokens.size() + existing;
}

} // namespace slang::parsing
