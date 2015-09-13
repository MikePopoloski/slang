#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "StringRef.h"
#include "Diagnostics.h"
#include "SourceTracker.h"
#include "Token.h"
#include "Lexer.h"
#include "StringTable.h"
#include "SyntaxFacts.h"
#include "Preprocessor.h"

namespace {

// TODO: copied from Lexer.cpp
template<typename T>
slang::ArrayRef<T> copyArray(slang::BumpAllocator& alloc, const slang::Buffer<T>& buffer) {
    uint32_t count = buffer.count();
    if (count == 0)
        return slang::ArrayRef<T>(nullptr, 0);

    const T* source = buffer.cbegin();
    T* dest = reinterpret_cast<T*>(alloc.allocate(count * sizeof(T)));
    for (uint32_t i = 0; i < count; i++)
        new (&dest[i]) T(*source++);
    return slang::ArrayRef<T>(dest, count);
}

}

namespace slang {

Preprocessor::Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceTracker(sourceTracker),
    alloc(alloc),
    diagnostics(diagnostics),
    currentLexer(nullptr),
    currentToken(nullptr) {

    keywordTable = getKeywordTable();
}

void Preprocessor::enterFile(SourceText source) {
    // TODO: expand this a bit
    enterFile(sourceTracker.track("unnamed"), source);
}

void Preprocessor::enterFile(FileID file, SourceText source) {
    // TODO: max include depth
    // create a new lexer for this file and push it onto the stack
    lexerStack.emplace_back(file, source, *this);
    currentLexer = &lexerStack.back();
}

Token* Preprocessor::lex() {
    while (true) {
        Token* token = consume();
        switch (token->kind) {
            case TokenKind::Identifier:
                return handleIdentifier(token);
            case TokenKind::EndOfFile:
                lexerStack.pop_back();
                currentLexer = lexerStack.empty() ? nullptr : &lexerStack.back();
                return token;
            case TokenKind::Directive:
                switch (token->directiveKind()) {
                    case TriviaKind::IncludeDirective:
                        token = handleInclude(token);
                        if (token)
                            return token;
                        break;
                }
                break;
            default:
                // pass through to the caller
                return token;
        }
    }
}

TokenKind Preprocessor::lookupKeyword(StringRef identifier) {
    // TODO: different tables based on state
    TokenKind kind;
    if (keywordTable->lookup(identifier, kind))
        return kind;
    return TokenKind::Unknown;
}

Trivia* Preprocessor::parseDirective(Lexer* lexer) {
    currentLexer = lexer;

    Token* directive = expect(TokenKind::Directive);
    switch (directive->directiveKind()) {
        case TriviaKind::IncludeDirective: return parseIncludeDirective(directive);
        default: return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
    }
}

Trivia* Preprocessor::parseIncludeDirective(Token* directive) {
    // next token should be a filename; lex that manually
    Token* fileName = currentLexer->lexIncludeFileName();
    Token* end = parseEndOfDirective();

    return alloc.emplace<IncludeDirectiveTrivia>(directive, fileName, end);
}

Token* Preprocessor::parseEndOfDirective() {
    return nullptr;
}

Token* Preprocessor::handleIdentifier(Token* token) {
    // this identifier might actually be a keyword token
    /*if (token->identifierType() != IdentifierType::Escaped) {
        TokenKind keywordKind;
        if (keywordTable->lookup(token->valueText(), keywordKind))
            return alloc.emplace<Token>(keywordKind, nullptr, token->trivia);
    }*/

    return token;
}

Token* Preprocessor::handleInclude(Token* directiveToken) {
    // next token needs to be the filename
    Token* token = consume();
    bool systemPath;
    switch (token->kind) {
        case TokenKind::IncludeFileName: systemPath = false; break;
        case TokenKind::EndOfDirective:
            // end of the line (or file) without finding the filename
            // issue an error and be on our merry way
            addError(DiagCode::ExpectedIncludeFileName);

            /*triviaBuffer.appendRange(directiveToken->trivia);
            triviaBuffer.append(Trivia(directiveToken->directiveKind(), StringRef()));*/

        case TokenKind::EndOfFile:
            addError(DiagCode::ExpectedIncludeFileName);
            //triviaBuffer.appendRange(token->trivia);
//            return alloc.emplace<Token>(TokenKind::EndOfFile, nullptr, copyArray(alloc, triviaBuffer));
        default:
            // we have junk here; scan the rest of the line and move on

            return nullptr;
    }

    SourceFile* file = sourceTracker.readHeader(currentLexer->getFile(), token->valueText(), systemPath);
    if (!file)
        return nullptr;

    // TODO: attach trivia

    enterFile(file->id, file->buffer);
}

void Preprocessor::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

Token* Preprocessor::peek() {
    if (!currentToken)
        currentToken = currentLexer->lex();
    return currentToken;
}

Token* Preprocessor::consume() {
    Token* result = peek();
    currentToken = nullptr;
    return result;
}

Token* Preprocessor::expect(TokenKind kind) {
    if (peek()->kind == kind)
        return consume();

    return Token::missing(alloc, kind);
}

}