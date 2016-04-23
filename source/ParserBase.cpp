#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "StringRef.h"
#include "SourceManager.h"
#include "Token.h"
#include "Diagnostics.h"
#include "Lexer.h"
#include "Preprocessor.h"
#include "ParserBase.h"

namespace slang {

ParserBase::ParserBase(Preprocessor& preprocessor) :
	window(preprocessor),
	alloc(preprocessor.getAllocator())
{
}

void ParserBase::reduceSkippedTokens(Buffer<Token*>& skipped, Buffer<Trivia>& trivia) {
	if (skipped.empty())
		return;
	trivia.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
	skipped.clear();
}

SyntaxNode* ParserBase::prependTrivia(SyntaxNode* node, Trivia* trivia) {
	if (trivia->kind != TriviaKind::Unknown && node)
		prependTrivia(node->getFirstToken(), trivia);
	return node;
}

Token* ParserBase::prependTrivia(Token* token, Trivia* trivia) {
	if (trivia->kind != TriviaKind::Unknown && token) {
		auto buffer = triviaPool.get();
		buffer.append(*trivia);
		buffer.appendRange(token->trivia);
		token->trivia = buffer.copy(alloc);

		*trivia = Trivia();
	}
	return token;
}

Token* ParserBase::prependTrivia(Token* token, Buffer<Trivia>& trivia) {
	ASSERT(token);
	trivia.appendRange(token->trivia);
	token->trivia = trivia.copy(alloc);
	trivia.clear();
	return token;
}

void ParserBase::prependTrivia(SyntaxNode* node, Buffer<Trivia>& trivia) {
	if (!trivia.empty()) {
		ASSERT(node);
		prependTrivia(node->getFirstToken(), trivia);
	}
}

SyntaxNode* ParserBase::prependSkippedTokens(SyntaxNode* node, Buffer<Token*>& tokens) {
	if (!tokens.empty()) {
		Trivia t(TriviaKind::SkippedTokens, tokens.copy(alloc));
		prependTrivia(node, &t);
		tokens.clear();
	}
	return node;
}

Token* ParserBase::prependSkippedTokens(Token* token, Buffer<Token*>& tokens) {
	if (!tokens.empty()) {
		Trivia t(TriviaKind::SkippedTokens, tokens.copy(alloc));
		prependTrivia(token, &t);
		tokens.clear();
	}
	return token;
}

void ParserBase::addError(DiagCode code) {
	// TODO: location
	window.tokenSource.getDiagnostics().emplace(code, SourceLocation(), 0);
}

Token* ParserBase::peek(int offset) {
	while (window.currentOffset + offset >= window.count)
		window.addNew();
	return window.buffer[window.currentOffset + offset];
}

Token* ParserBase::peek() {
	if (!window.currentToken) {
		if (window.currentOffset >= window.count)
			window.addNew();
		window.currentToken = window.buffer[window.currentOffset];
	}
	return window.currentToken;
}

bool ParserBase::peek(TokenKind kind) {
	return peek()->kind == kind;
}

Token* ParserBase::consume() {
	auto result = peek();
	window.moveToNext();
	return result;
}

Token* ParserBase::consumeIf(TokenKind kind) {
	auto result = peek();
	if (result->kind != kind)
		return nullptr;

	window.moveToNext();
	return result;
}

Token* ParserBase::expect(TokenKind kind) {
	auto result = peek();
	if (result->kind != kind) {
		// report an error here for the missing token
		addError(DiagCode::SyntaxError);
		return Token::missing(alloc, kind, result->location);
	}

	window.moveToNext();
	return result;
}

void ParserBase::Window::addNew() {
	if (count >= capacity) {
		// shift tokens to the left if we are too far to the right
		if (currentOffset > (capacity >> 1)) {
			int shift = count - currentOffset;
			if (shift > 0)
				memmove(buffer, buffer + currentOffset, shift * sizeof(Token*));

			count -= currentOffset;
			currentOffset = 0;
		}
		else {
			Token** newBuffer = new Token*[capacity * 2];
			memcpy(newBuffer, buffer, count * sizeof(Token*));

			delete[] buffer;
			buffer = newBuffer;
		}
	}
	buffer[count] = tokenSource.next();
	count++;
}

void ParserBase::Window::moveToNext() {
	currentToken = nullptr;
	currentOffset++;
}

}