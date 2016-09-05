#include "ParserBase.h"

#include "BumpAllocator.h"
#include "Preprocessor.h"

namespace slang {

static bool reportErrorAdjacent(TokenKind kind) {
    switch (kind) {
        case TokenKind::OpenBracket:
        case TokenKind::OpenParenthesis:
        case TokenKind::OpenParenthesisStar:
        case TokenKind::OpenParenthesisStarCloseParenthesis:
        case TokenKind::Semicolon:
        case TokenKind::Colon:
        case TokenKind::DoubleColon:
        case TokenKind::Comma:
        case TokenKind::Dot:
            return true;
        default:
            return false;
    }
}

ParserBase::ParserBase(Preprocessor& preprocessor) :
    window(preprocessor),
    alloc(preprocessor.getAllocator())
{
}

void ParserBase::reduceSkippedTokens(Buffer<Token>& skipped, Buffer<Trivia>& trivia) {
    if (skipped.empty())
        return;
    trivia.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
    skipped.clear();
}

SyntaxNode* ParserBase::prependTrivia(SyntaxNode* node, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && node) {
        Token newToken = prependTrivia(node->getFirstToken(), trivia);
        ASSERT(node->replaceFirstToken(newToken));
    }
    return node;
}

Token ParserBase::prependTrivia(Token token, Trivia* trivia) {
    if (trivia->kind != TriviaKind::Unknown && token) {
        auto buffer = triviaPool.get();
        buffer.append(*trivia);
        buffer.appendRange(token.trivia());

        token = token.withTrivia(alloc, buffer.copy(alloc));
        *trivia = Trivia();
    }
    return token;
}

Token ParserBase::prependTrivia(Token token, Buffer<Trivia>& trivia) {
    ASSERT(token);
    trivia.appendRange(token.trivia());
    token = token.withTrivia(alloc, trivia.copy(alloc));
    trivia.clear();
    return token;
}

void ParserBase::prependTrivia(SyntaxNode* node, Buffer<Trivia>& trivia) {
    if (!trivia.empty()) {
        ASSERT(node);
        Token newToken = prependTrivia(node->getFirstToken(), trivia);
        ASSERT(node->replaceFirstToken(newToken));
    }
}

SyntaxNode* ParserBase::prependSkippedTokens(SyntaxNode* node, Buffer<Token>& tokens) {
    if (!tokens.empty()) {
        Trivia t(TriviaKind::SkippedTokens, tokens.copy(alloc));
        prependTrivia(node, &t);
        tokens.clear();
    }
    return node;
}

Token ParserBase::prependSkippedTokens(Token token, Buffer<Token>& tokens) {
    if (!tokens.empty()) {
        Trivia t(TriviaKind::SkippedTokens, tokens.copy(alloc));
        prependTrivia(token, &t);
        tokens.clear();
    }
    return token;
}

Diagnostics& ParserBase::getDiagnostics() {
    return window.tokenSource.getDiagnostics();
}

void ParserBase::addError(DiagCode code) {
    // TODO: location
    window.tokenSource.getDiagnostics().emplace(code, SourceLocation());
}

Diagnostic& ParserBase::addError(DiagCode code, SourceLocation location) {
    return getDiagnostics().add(code, location);
}

Token ParserBase::peek(int offset) {
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
    return result;
}

Token ParserBase::consumeIf(TokenKind kind) {
    auto result = peek();
    if (result.kind != kind)
        return Token();

    window.moveToNext();
    return result;
}

Token ParserBase::expect(TokenKind kind) {
    // keep this method small so that it gets inlined
    auto result = peek();
    if (result.kind != kind)
        return createExpectedToken(result, kind);

    window.moveToNext();
    return result;
}

Token ParserBase::createExpectedToken(Token actual, TokenKind expected) {
    SourceLocation location;
    if (!window.lastConsumed || !reportErrorAdjacent(expected))
        location = actual.location();
    else {
        location = window.lastConsumed.location();
        location = location + window.lastConsumed.rawText().length();
    }

    // report an error here for the missing token
    switch (expected) {
        case TokenKind::Identifier: addError(DiagCode::ExpectedIdentifier, location); break;
        default: addError(DiagCode::ExpectedToken, location) << getTokenKindText(expected); break;
    }
    return Token::createMissing(alloc, expected, location);
}

void ParserBase::Window::addNew() {
    if (count >= capacity) {
        // shift tokens to the left if we are too far to the right
        if (currentOffset > (capacity >> 1)) {
            int shift = count - currentOffset;
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

}