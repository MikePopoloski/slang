#include <cstdint>
#include <string>
#include <ostream>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringRef.h"
#include "Buffer.h"
#include "Token.h"
#include "Trivia.h"

namespace slang {

void SimpleTrivia::writeTo(Buffer<char>& buffer) {
    buffer.appendRange(rawText);
}

void SimpleDirectiveTrivia::writeTo(Buffer<char>& buffer) {
    directive->writeTo(buffer, true);
}

void IncludeDirectiveTrivia::writeTo(Buffer<char>& buffer) {
    directive->writeTo(buffer, true);
}

void SkippedTokensTrivia::writeTo(Buffer<char>& buffer) {
    for (auto& token : tokens)
        token->writeTo(buffer, true);
}

MacroFormalArgumentList::MacroFormalArgumentList(
    Token* openParen,
    ArrayRef<MacroFormalArgument*> args,
    ArrayRef<Token*> commaSeparators,
    Token* closeParen
) :
    openParen(openParen),
    args(args),
    commaSeparators(commaSeparators),
    closeParen(closeParen)
{
}

DefineDirectiveTrivia::DefineDirectiveTrivia(
    Token* directive,
    Token* name,
    Token* endOfDirective,
    MacroFormalArgumentList* formalArguments,
    ArrayRef<Token*> body
) :
    Trivia(TriviaKind::DefineDirective),
    directive(directive),
    name(name),
    endOfDirective(endOfDirective),
    formalArguments(formalArguments),
    body(body)
{
}

void DefineDirectiveTrivia::writeTo(Buffer<char>& buffer) {
    directive->writeTo(buffer, true);
}

}