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
// to let us provide tokens from a lexer on the include stack. It's not pretty,
// but it's necessary to present a nicer lexer interface to the user.
Token* Preprocessor::lex(Lexer* current) {
    // quick check for the common case
    if (!hasTokenSource)
        return nullptr;

    // check if we're expanding a macro
    if (currentMacro.isActive())
        return currentMacro.next();

    if (lexerStack.empty()) {
        hasTokenSource = false;
        return nullptr;
    }

    // avoid an infinite recursion of death when called from an include file lexer
    if (&lexerStack.back() == current)
        return nullptr;

    while (true) {
        Token* result = lexerStack.back().lex();
        if (result->kind != TokenKind::EndOfFile)
            return result;

        // end of file; pop and move to next lexer
        lexerStack.pop_back();
        if (lexerStack.empty()) {
            hasTokenSource = false;
            return nullptr;
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
        case TriviaKind::IncludeDirective: return handleIncludeDirective(directive);
        case TriviaKind::ResetAllDirective: return handleResetAllDirective(directive);
        case TriviaKind::DefineDirective: return handleDefineDirective(directive);
        case TriviaKind::MacroUsage: return handleMacroUsage(directive);
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

    StringRef path = fileName->valueText();
    if (path.length() < 3)
        addError(DiagCode::ExpectedIncludeFileName);
    else {
        // remove delimiters
        path = path.subString(1, path.length() - 2);
        SourceFile* source = sourceTracker.readHeader(currentLexer->getFile(), path, false);
        if (!source)
            addError(DiagCode::CouldNotOpenIncludeFile);
        else if (lexerStack.size() >= MaxIncludeDepth)
            addError(DiagCode::ExceededMaxIncludeDepth);
        else {
            // push the new lexer onto the include stack
            // the active lexer will pull tokens from it
            hasTokenSource = true;
            lexerStack.emplace_back(source->id, source->buffer, *this);
        }
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

    DefineDirectiveTrivia* result = alloc.emplace<DefineDirectiveTrivia>(
        directive,
        name,
        consume(),
        formalArguments,
        body.copy(alloc)
    );

    macros.emplace(name->valueText().intern(alloc), result);
    return result;
}

Trivia* Preprocessor::handleMacroUsage(Token* directive) {
    // TODO: create specialized trivia for this
    // try to look up the macro in our map
    auto it = macros.find(directive->valueText().subString(1));
    if (it == macros.end()) {
        addError(DiagCode::UnknownDirective);
        return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
    }

    DefineDirectiveTrivia* macro = it->second;
    currentMacro.start(macro);
    hasTokenSource = true;

    return alloc.emplace<SimpleDirectiveTrivia>(directive->directiveKind(), directive, parseEndOfDirective());
}

Token* Preprocessor::parseEndOfDirective() {
    // consume all extraneous tokens as SkippedToken trivia
    auto skipped = tokenPool.get();
    if (peek()->kind != TokenKind::EndOfDirective) {
        addError(DiagCode::ExpectedEndOfDirective);
        do {
            skipped.append(consume());
        } while (peek()->kind != TokenKind::EndOfDirective);
    }

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

void MacroExpander::start(DefineDirectiveTrivia* macro) {
    // expand all tokens recursively and store them in our buffer
    tokens.clear();
    expand(macro);
    current = tokens.begin();
    if (current == tokens.end())
        current = nullptr;
}

Token* MacroExpander::next() {
    Token* result = *current;
    current++;
    if (current == tokens.end())
        current = nullptr;

    return result;
}

bool MacroExpander::isActive() const {
    return current != nullptr;
}

void MacroExpander::expand(DefineDirectiveTrivia* macro) {
    if (!macro->formalArguments) {
        // simple macro; just take body tokens
        tokens.appendRange(macro->body);
    }
}

}