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
    diagnostics(diagnostics)
{
    keywordTable = getKeywordTable();
}

void Preprocessor::pushSource(SourceText source, FileID file) {
	ASSERT(sourceStack.size() < MaxSourceDepth);
	auto lexer = alloc.emplace<Lexer>(file, source, alloc, diagnostics);
	sourceStack.push_back(lexer);
}

FileID Preprocessor::getCurrentFile() {
	// figure out which lexer is highest in our source stack
	for (auto it = sourceStack.rbegin(); it != sourceStack.rend(); it++) {
		if (it->kind == Source::LEXER)
			return it->lexer->getFile();
	}
	return FileID();
}

Token* Preprocessor::next() {
	return next(LexerMode::Normal);
}

Token* Preprocessor::next(LexerMode mode) {
	// common case: lex a token and return it
	auto token = nextRaw(mode);
	if (token->kind != TokenKind::Directive)
		return token;

	// burn through any preprocessor directives we find and convert them to trivia
	auto trivia = triviaPool.get();
	do {
		// TODO: handle all directive types
		// TODO: check keyword eligibility
		switch (token->directiveKind()) {
			case SyntaxKind::IncludeDirective:
				trivia.append(handleIncludeDirective(token));
				break;
			case SyntaxKind::ResetAllDirective:
				trivia.append(handleResetAllDirective(token));
				break;
			case SyntaxKind::DefineDirective:
				trivia.append(handleDefineDirective(token));
				break;
			case SyntaxKind::MacroUsage:
				trivia.append(handleMacroUsage(token));
				break;
			case SyntaxKind::UndefineAllDirective:
			case SyntaxKind::UnconnectedDriveDirective:
			case SyntaxKind::NoUnconnectedDriveDirective:
			case SyntaxKind::CellDefineDirective:
			case SyntaxKind::EndCellDefineDirective:
			default:
				trivia.append(createSimpleDirective(token));
				break;
		}
		token = nextRaw(mode);
	} while (token->kind == TokenKind::Directive);

	trivia.appendRange(token->trivia);
	token->trivia = trivia.copy(alloc);
	return token;
}

Token* Preprocessor::nextRaw(LexerMode mode) {
	// it's possible we have a token buffered from looking ahead when handling a directive
	if (currentToken) {
		auto result = currentToken;
		currentToken = nullptr;
		return result;
	}

	// if this assert fires, the user disregarded an EoF and kept calling next()
	ASSERT(!sourceStack.empty());
	
	// Pull the next token from the active source (macro or file).
	// This is the common case.
	Token* token = nullptr;
	auto& source = sourceStack.back();
	switch (source.kind) {
		case Source::MACRO:
			token = source.macro->next();
			if (source.macro->done())
				sourceStack.pop_back();
			return token;
		case Source::LEXER:
			token = source.lexer->lex(mode);
			if (token->kind != TokenKind::EndOfFile)
				return token;

			// don't return EndOfFile tokens for included files, fall
			// through to loop to merge trivia
			sourceStack.pop_back();
			if (sourceStack.empty())
				return token;
	}

	// Rare case: we have an EoF from an include file... we don't want to return
	// that one, but we do want to merge its trivia with whatever comes next.
	auto trivia = triviaPool.get();
	trivia.appendRange(token->trivia);

	while (true) {
		bool keepGoing = false;
		auto& nextSource = sourceStack.back();
		switch (nextSource.kind) {
			case Source::MACRO:
				token = nextSource.macro->next();
				if (nextSource.macro->done())
					sourceStack.pop_back();
				break;
			case Source::LEXER: {
				token = nextSource.lexer->lex(mode);
				if (token->kind != TokenKind::EndOfFile)
					break;

				sourceStack.pop_back();
				if (sourceStack.empty())
					break;

				// if we have another `include EoF, just append the trivia and keep going
				keepGoing = true;
			}
		}
		trivia.appendRange(token->trivia);
		if (!keepGoing) {
			// finally found a real token to return, so update trivia and get out of here
			token->trivia = trivia.copy(alloc);
			return token;
		}
	}
}

Trivia Preprocessor::handleIncludeDirective(Token* directive) {
    // next token should be a filename
	Token* fileName = next(LexerMode::IncludeFileName);
	Token* end = parseEndOfDirective();

	StringRef path = fileName->valueText();
	if (path.length() < 3)
		addError(DiagCode::ExpectedIncludeFileName);
	else {
		// remove delimiters
		path = path.subString(1, path.length() - 2);
		SourceFile* file = sourceTracker.readHeader(getCurrentFile(), path, false);
		if (!file)
			addError(DiagCode::CouldNotOpenIncludeFile);
		else if (sourceStack.size() >= MaxSourceDepth)
			addError(DiagCode::ExceededMaxIncludeDepth);
		else
			pushSource(file->buffer, file->id);
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

	// TODO: don't lex in directive mode here

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

	auto macroSource = alloc.emplace<MacroExpander>(macro, actualArgs);
	sourceStack.push_back(macroSource);

	auto syntax = alloc.emplace<MacroUsageSyntax>(directive, actualArgs);
	return Trivia(TriviaKind::Directive, syntax);
}

Token* Preprocessor::parseEndOfDirective() {
    // consume all extraneous tokens as SkippedToken trivia
    auto skipped = tokenPool.get();
    if (!peek(TokenKind::EndOfDirective)) {
        addError(DiagCode::ExpectedEndOfDirective);
        do {
            skipped.append(consume());
        } while (!peek(TokenKind::EndOfDirective));
    }

    Token* eod = consume();
    if (skipped.empty())
        return eod;

    // splice together the trivia
	auto trivia = triviaPool.get();
	trivia.append(Trivia(TriviaKind::SkippedTokens, skipped.copy(alloc)));
	trivia.appendRange(eod->trivia);

    return Token::createSimple(alloc, TokenKind::EndOfDirective, trivia.copy(alloc));
}

Trivia Preprocessor::createSimpleDirective(Token* directive) {
    DirectiveSyntax* syntax = alloc.emplace<SimpleDirectiveSyntax>(directive->directiveKind(), directive, parseEndOfDirective());
    return Trivia(TriviaKind::Directive, syntax);
}

Token* Preprocessor::peek() {
	if (!currentToken)
		currentToken = next(LexerMode::Directive);
	return currentToken;
}

Token* Preprocessor::consume() {
	auto result = peek();
	currentToken = nullptr;
	return result;
}

Token* Preprocessor::expect(TokenKind kind) {
	auto result = peek();
	if (result->kind != kind) {
		// report an error here for the missing token
		// TODO: location info
		addError(DiagCode::SyntaxError);
		return Token::missing(alloc, kind);
	}

	currentToken = nullptr;
	return result;
}

void Preprocessor::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

MacroExpander::MacroExpander(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs) {
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