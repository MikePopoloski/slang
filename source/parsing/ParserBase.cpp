//------------------------------------------------------------------------------
// ParserBase.cpp
// Base class for parsing.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/parsing/ParserBase.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

ParserBase::ParserBase(Preprocessor& preprocessor) :
    alloc(preprocessor.getAllocator()), window(preprocessor) {
}

void ParserBase::prependSkippedTokens(Token& token) {
    SmallVectorSized<Trivia, 8> buffer;
    buffer.append(Trivia{ TriviaKind::SkippedTokens, skippedTokens.copy(alloc) });
    buffer.appendRange(token.trivia());

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
    ASSERT(window.currentToken);
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
    return result;
}

Token ParserBase::consumeIf(TokenKind kind) {
    if (peek(kind))
        return consume();
    return Token();
}

Token ParserBase::expect(TokenKind kind) {
    // keep this method small so that it gets inlined
    auto result = peek();
    if (result.kind != kind)
        result = Token::createExpected(alloc, getDiagnostics(), result, kind, window.lastConsumed);
    else
        window.moveToNext();

    if (!skippedTokens.empty())
        prependSkippedTokens(result);

    return result;
}

void ParserBase::skipToken(std::optional<DiagCode> diagCode) {
    bool haveDiag = haveDiagAtCurrentLoc();
    auto token = peek();
    skippedTokens.append(token);
    window.moveToNext();

    if (diagCode && !haveDiag)
        addDiag(*diagCode, token.location()) << token.range();

    // If the token we're skipping is an opening paren / bracket / brace,
    // skip everything up to the corresponding closing token, otherwise we're
    // pretty much guaranteed to report a bunch of spurious errors inside it.
    TokenKind skipKind = getSkipToKind(token.kind);
    if (skipKind != TokenKind::Unknown) {
        SmallVectorSized<TokenKind, 16> delimStack;
        while (true) {
            token = peek();
            skippedTokens.append(token);
            window.moveToNext();

            if (token.kind == skipKind ||
                (skipKind == TokenKind::EndKeyword && isEndKeyword(token.kind))) {
                if (delimStack.empty())
                    break;

                skipKind = delimStack.back();
                delimStack.pop();
            }
            else {
                TokenKind newSkipKind = getSkipToKind(token.kind);
                if (newSkipKind != TokenKind::Unknown) {
                    delimStack.append(skipKind);
                    skipKind = newSkipKind;
                }
            }
        }
    }
}

void ParserBase::pushTokens(span<const Token> tokens) {
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
    return !diags.empty() && diags.getNumErrors() &&
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
    diag << getTokenKindText(window.lastConsumed.kind);
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

void ParserBase::Window::insertHead(span<const Token> tokens) {
    if (currentOffset >= tokens.size()) {
        currentOffset -= tokens.size();
        memcpy(buffer + currentOffset, tokens.data(), tokens.size() * sizeof(Token));
        return;
    }

    size_t existing = count - currentOffset;
    ASSERT(tokens.size() + existing < capacity);

    memmove(buffer + tokens.size(), buffer + currentOffset, existing * sizeof(Token));
    memcpy(buffer, tokens.data(), tokens.size() * sizeof(Token));

    currentOffset = 0;
    count = tokens.size() + existing;
}

} // namespace slang