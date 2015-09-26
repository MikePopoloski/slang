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
        case TriviaKind::IncludeDirective: return handleIncludeDirective(directive);
        case TriviaKind::ResetAllDirective: return handleResetAllDirective(directive);
        case TriviaKind::UndefineAllDirective:
        case TriviaKind::UnconnectedDriveDirective:
        case TriviaKind::NoUnconnectedDriveDirective:
        case TriviaKind::CellDefineDirective:
        case TriviaKind::EndCellDefineDirective:
        default: return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
    }
}

Trivia* Preprocessor::handleIncludeDirective(Token* directive) {
    // next token should be a filename; lex that manually
    Token* fileName = currentLexer->lexIncludeFileName();
    Token* end = parseEndOfDirective();

    // TODO: check missing or short filename
    StringRef path = fileName->valueText();
    path = path.subString(1, path.length() - 2);
    SourceFile* source = sourceTracker.readHeader(currentLexer->getFile(), path, false);
    if (!source)
        addError(DiagCode::CouldNotOpenIncludeFile);
    else if (lexerStack.size() >= MaxIncludeDepth)
        addError(DiagCode::ExceededMaxIncludeDepth);
    else {
        // push the new lexer onto the include stack
        // the active lexer will pull tokens from it
        lexerStack.emplace_back(source->id, source->buffer, *this);
    }

    return alloc.emplace<IncludeDirectiveTrivia>(directive, fileName, end);
}

Trivia* Preprocessor::handleResetAllDirective(Token* directive) {
    // TODO: reset all preprocessor state here
    return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
}

Trivia* Preprocessor::handleDefineDirective(Token* directive) {
    // next token should be the macro name
    Token* name = expect(TokenKind::Identifier);

    // check if this is a function-like macro, which requires an opening paren with no leading space
    MacroFormalArgumentList* formalArguments = nullptr;
    Token* maybeParen = peek();
    if (maybeParen->kind == TokenKind::OpenParenthesis && maybeParen->trivia.empty()) {
        // parse all formal arguments
        auto arguments = argumentPool.get();
        consume();
        while (true) {
            Token* arg = expect(TokenKind::Identifier);
            TokenKind kind = peek()->kind;
            if (kind == TokenKind::Equals) {
               // parseMacroDefault();
                kind = peek()->kind;
            }

            arguments.append(alloc.emplace<MacroFormalArgument>(arg, nullptr));

            if (kind == TokenKind::CloseParenthesis)
                break;

            // TODO: handle errors
            if (kind != TokenKind::Comma) {
            }
            else {
            }
        }

        formalArguments = alloc.emplace<MacroFormalArgumentList>(
            maybeParen,
            arguments.copy(alloc),
            nullptr, // TODO
            consume() // TODO
        );
    }
    
    // consume all remaining tokens as macro text
    auto body = tokenPool.get();
    while (peek()->kind != TokenKind::EndOfDirective)
        body.append(consume());

    return alloc.emplace<DefineDirectiveTrivia>(
        directive,
        name,
        consume(),
        formalArguments,
        body.copy(alloc)
    );
}

Token* Preprocessor::parseEndOfDirective() {
    // consume all extraneous tokens as SkippedToken trivia
    // TODO: error reporting
    auto skipped = tokenPool.get();
    while (peek()->kind != TokenKind::EndOfDirective)
        skipped.append(consume());

    Token* eod = consume();
    if (skipped.empty())
        return eod;

    // splice together the trivia
    triviaBuffer.clear();
    triviaBuffer.append(alloc.emplace<SkippedTokensTrivia>(skipped.copy(alloc)));
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