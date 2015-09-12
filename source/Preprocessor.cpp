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
#include "TokenConsumer.h"
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
    sourceTracker(sourceTracker), alloc(alloc), diagnostics(diagnostics) {

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
    setSource(&lexerStack.back());
}

Token* Preprocessor::lex() {
    while (true) {
        Token* token = consume();
        switch (token->kind) {
            case TokenKind::Identifier:
                return handleIdentifier(token);
            case TokenKind::EndOfFile:
                lexerStack.pop_back();
                if (lexerStack.empty())
                    setSource(nullptr);
                else
                    setSource(&lexerStack.back());
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

void Preprocessor::parseDirective(Lexer* lexer) {
    setSource(lexer);

    Token* directive = expect(TokenKind::Directive);
    switch (getDirectiveKind(directive->valueText())) {
        case TriviaKind::IncludeDirective:
            parseIncludeDirective();
            break;
    }
}

void Preprocessor::parseIncludeDirective() {
    // next token should be a filename; lex that manually
    Token* fileName = getSource()->lexIncludeFileName();
    Token* end = parseEndOfDirective();
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
            convertDirectiveToTrivia(directiveToken);
            //triviaBuffer.appendRange(token->trivia);
//            return alloc.emplace<Token>(TokenKind::EndOfFile, nullptr, copyArray(alloc, triviaBuffer));
        default:
            // we have junk here; scan the rest of the line and move on

            return nullptr;
    }

    SourceFile* file = sourceTracker.readHeader(getSource()->getFile(), token->valueText(), systemPath);
    if (!file)
        return nullptr;

    // TODO: attach trivia

    enterFile(file->id, file->buffer);
}

void Preprocessor::convertDirectiveToTrivia(Token* directive) {
//    triviaBuffer.appendRange(directive->trivia);
  //  triviaBuffer.append(Trivia(directive->directiveKind(), StringRef()));
}

void Preprocessor::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

}