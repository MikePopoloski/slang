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
#include "Preprocessor.h"
#include "AllSyntax.h"

namespace slang {

Preprocessor::Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    sourceTracker(sourceTracker),
    alloc(alloc),
    diagnostics(diagnostics),
    currentLexer(nullptr) {

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

Trivia Preprocessor::parseDirective(Lexer* lexer) {
    currentLexer = lexer;
    window.setSource(lexer);

    Token* directive = expect(TokenKind::Directive);
    switch (directive->directiveKind()) {
        case SyntaxKind::IncludeDirective: return handleIncludeDirective(directive);
        case SyntaxKind::ResetAllDirective: return handleResetAllDirective(directive);
        case SyntaxKind::DefineDirective: return handleDefineDirective(directive);
        case SyntaxKind::MacroUsage: return handleMacroUsage(directive);
        case SyntaxKind::UndefineAllDirective:
        case SyntaxKind::UnconnectedDriveDirective:
        case SyntaxKind::NoUnconnectedDriveDirective:
        case SyntaxKind::CellDefineDirective:
        case SyntaxKind::EndCellDefineDirective:
        default: return createSimpleDirective(directive);
    }
}

Trivia Preprocessor::handleIncludeDirective(Token* directive) {
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

    auto syntax = alloc.emplace<IncludeDirectiveSyntax>(directive, fileName, end);
    return Trivia(TriviaKind::Directive, syntax);
}

Trivia Preprocessor::handleResetAllDirective(Token* directive) {
    // TODO: reset all preprocessor state here
    return createSimpleDirective(directive);
}

ArrayRef<Token*> Preprocessor::parseMacroArg() {
    auto tokens = tokenPool.get();

    // comma and right parenthesis only end the default token list if they are
    // not inside a nested pair of (), [], or {}
    // otherwise, keep swallowing tokens as part of the default
    while (true) {
        auto kind = peek()->kind;
        if (kind == TokenKind::EndOfDirective) {
            if (delimPairStack.empty())
                addError(DiagCode::ExpectedEndOfMacroArgs);
            else
                addError(DiagCode::UnbalancedMacroArgDims);
            delimPairStack.clear();
            break;
        }

        if (delimPairStack.empty()) {
            if ((kind == TokenKind::Comma || kind == TokenKind::CloseParenthesis))
                break;
        }
        else if (delimPairStack.last() == kind)
            delimPairStack.pop();

        tokens.append(consume());
        switch (kind) {
            case TokenKind::OpenParenthesis:
                delimPairStack.append(TokenKind::CloseParenthesis);
                break;
            case TokenKind::OpenBrace:
                delimPairStack.append(TokenKind::CloseBrace);
                break;
            case TokenKind::OpenBracket:
                delimPairStack.append(TokenKind::CloseBracket);
                break;
        }
    }
    return tokens.copy(alloc);
}

Trivia Preprocessor::handleDefineDirective(Token* directive) {
    // next token should be the macro name
    auto name = expect(TokenKind::Identifier);

    // check if this is a function-like macro, which requires an opening paren with no leading space
    MacroFormalArgumentListSyntax* formalArguments = nullptr;
    if (peek(TokenKind::OpenParenthesis) && peek()->trivia.empty()) {
        // parse all formal arguments
        auto openParen = consume();
        auto arguments = syntaxPool.get();
        while (true) {
            auto arg = expect(TokenKind::Identifier);

            MacroArgumentDefaultSyntax* argDef = nullptr;
            if (peek(TokenKind::Equals)) {
                auto equals = consume();
                argDef = alloc.emplace<MacroArgumentDefaultSyntax>(equals, parseMacroArg());
            }

            arguments.append(alloc.emplace<MacroFormalArgumentSyntax>(arg, argDef));

            auto kind = peek()->kind;
            if (kind == TokenKind::CloseParenthesis)
                break;
            else if (kind == TokenKind::Comma)
                arguments.append(consume());
            else {
                // TODO: skipped tokens
            }
        }
        formalArguments = alloc.emplace<MacroFormalArgumentListSyntax>(
            openParen,
            arguments.copy(alloc),
            expect(TokenKind::CloseParenthesis)
        );
    }
    
    // consume all remaining tokens as macro text
    auto body = tokenPool.get();
    while (!peek(TokenKind::EndOfDirective))
        body.append(consume());

    auto result = alloc.emplace<DefineDirectiveSyntax>(
        directive,
        name,
        formalArguments,
        body.copy(alloc),
        consume()
    );

    macros.emplace(name->valueText().intern(alloc), result);
    return Trivia(TriviaKind::Directive, result);
}

Trivia Preprocessor::handleMacroUsage(Token* directive) {
    // try to look up the macro in our map
    auto it = macros.find(directive->valueText().subString(1));
    if (it == macros.end()) {
        addError(DiagCode::UnknownDirective);
        return createSimpleDirective(directive);
    }

    DefineDirectiveSyntax* macro = it->second;

	MacroActualArgumentListSyntax* actualArgs = nullptr;
    if (macro->formalArguments) {
        // macro has arguments, so we expect to see them here
		if (!peek(TokenKind::OpenParenthesis)) {
			addError(DiagCode::ExpectedMacroArgs);
			return createSimpleDirective(directive);
		}

		auto openParen = consume();
		auto arguments = syntaxPool.get();
		while (true) {
			auto arg = parseMacroArg();
			arguments.append(alloc.emplace<MacroActualArgumentSyntax>(arg));

			auto kind = peek()->kind;
			if (kind == TokenKind::CloseParenthesis)
				break;
			else if (kind == TokenKind::Comma)
				arguments.append(consume());
			else {
				// TODO: skipped tokens
			}
		}

		auto closeParen = expect(TokenKind::CloseParenthesis);
		actualArgs = alloc.emplace<MacroActualArgumentListSyntax>(openParen, arguments.copy(alloc), closeParen);
    }

    currentMacro.start(macro, actualArgs);
    hasTokenSource = true;

	auto syntax = alloc.emplace<MacroUsageSyntax>(directive, actualArgs);
	return Trivia(TriviaKind::Directive, syntax);
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
    triviaBuffer.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
    triviaBuffer.appendRange(eod->trivia);

    return Token::createSimple(alloc, TokenKind::EndOfDirective, triviaBuffer.copy(alloc));
}

Trivia Preprocessor::createSimpleDirective(Token* directive) {
    DirectiveSyntax* syntax = alloc.emplace<SimpleDirectiveSyntax>(directive->directiveKind(), directive, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, syntax);
}

void Preprocessor::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

void MacroExpander::start(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs) {
    // expand all tokens recursively and store them in our buffer
    tokens.clear();
    expand(macro, actualArgs);
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

void MacroExpander::expand(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs) {
    if (!macro->formalArguments) {
        // simple macro; just take body tokens
        tokens.appendRange(macro->body);
		return;
    }


}

}