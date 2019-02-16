//------------------------------------------------------------------------------
// ParserBase.cpp
// Base class for parsing.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/parsing/ParserBase.h"

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
    auto token = peek();
    skippedTokens.append(token);
    window.moveToNext();

    if (diagCode)
        addDiag(*diagCode, token.location()) << token.range();
}

Token ParserBase::missingToken(TokenKind kind, SourceLocation location) {
    return Token::createMissing(alloc, kind, location);
}

Token ParserBase::getLastConsumed() const {
    return window.lastConsumed;
}

void ParserBase::Window::addNew() {
    if (count >= capacity) {
        // shift tokens to the left if we are too far to the right
        if (currentOffset > (capacity >> 1)) {
            uint32_t shift = count - currentOffset;
            if (shift > 0)
                memmove(buffer, buffer + currentOffset, shift * sizeof(Token));

            count -= currentOffset;
            currentOffset = 0;
        }
        else {
            capacity *= 2;
            Token* newBuffer = new Token[capacity];
            memcpy(newBuffer, buffer, count * sizeof(Token));

            delete[] buffer;
            buffer = newBuffer;
        }
    }
    buffer[count] = tokenSource.next();
    count++;
}

void ParserBase::Window::moveToNext() {
    lastConsumed = currentToken;
    currentToken = Token();
    currentOffset++;
}

} // namespace slang