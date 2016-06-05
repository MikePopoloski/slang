#pragma once

#include "Token.h"

namespace slang {

class BumpAllocator;
struct SourceBuffer;
struct DefineDirectiveSyntax;
struct MacroFormalArgumentSyntax;
struct MacroActualArgumentListSyntax;

class MacroExpander {
public:
    MacroExpander(BumpAllocator& alloc, DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs);
    Token* next();

    bool done() const;

private:
    BumpAllocator& alloc;
    Buffer<Token*> tokens;
    Token** current = nullptr;

    void expand(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs);
};

}