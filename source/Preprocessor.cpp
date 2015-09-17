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

namespace slang {

Preprocessor::Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceTracker(sourceTracker),
    alloc(alloc),
    diagnostics(diagnostics),
    currentLexer(nullptr),
    currentToken(nullptr) {

    keywordTable = getKeywordTable();
}

// This function is a little weird; it's called from within the active lexer
// to let us provide tokens from a lexer on the include stack.
Token* Preprocessor::lex(Lexer* current) {
    if (lexerStack.empty())
        return nullptr;

    // avoid an infinite recursion of death
    Lexer* top = &lexerStack.back();
    if (top == current)
        return nullptr;

    return lexerStack.back().lex();
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
        case TriviaKind::ResetAllDirective:
        case TriviaKind::UndefineAllDirective:
        case TriviaKind::UnconnectedDriveDirective:
        case TriviaKind::NoUnconnectedDriveDirective:
        case TriviaKind::CellDefineDirective:
        case TriviaKind::EndCellDefineDirective:
        default: return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
    }
}

Trivia* Preprocessor::parseIncludeDirective(Token* directive) {
    // next token should be a filename; lex that manually
    Token* fileName = currentLexer->lexIncludeFileName();
    Token* end = parseEndOfDirective();

    // TODO: check missing or short filename
    StringRef path = fileName->valueText();
    path = path.subString(1, path.length() - 2);
    SourceFile* source = sourceTracker.readHeader(currentLexer->getFile(), path, false);
    if (!source)
        addError(DiagCode::CantOpenIncludeFile);
    else if (lexerStack.size() >= MaxIncludeDepth)
        addError(DiagCode::ExceededMaxIncludeDepth);
    else {
        // push the new lexer onto the include stack
        // the active lexer will pull tokens from it
        lexerStack.emplace_back(source->id, source->buffer, *this);
    }

    return alloc.emplace<IncludeDirectiveTrivia>(directive, fileName, end);
}

Token* Preprocessor::parseEndOfDirective() {
    // consume all extraneous tokens as SkippedToken trivia
    // TODO: error reporting
    tokenBuffer.clear();
    while (peek()->kind != TokenKind::EndOfDirective)
        tokenBuffer.append(consume());

    Token* eod = consume();
    if (tokenBuffer.empty())
        return eod;

    // splice together the trivia
    triviaBuffer.clear();
    triviaBuffer.append(alloc.emplace<SkippedTokensTrivia>(tokenBuffer.copy(alloc)));
    triviaBuffer.appendRange(eod->trivia);

    return Token::createSimple(alloc, TokenKind::EndOfDirective, triviaBuffer.copy(alloc));
}

void Preprocessor::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

Token* Preprocessor::peek() {
    if (!currentToken)
        currentToken = currentLexer->lexDirectiveMode();
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