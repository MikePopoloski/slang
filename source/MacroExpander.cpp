#include "MacroExpander.h"

#include "AllSyntax.h"

namespace slang {

MacroExpander::MacroExpander(BumpAllocator& alloc, DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs) :
    alloc(alloc)
{
    // expand all tokens recursively and store them in our buffer
    expand(macro, actualArgs);
    current = tokens.begin();
    if (current == tokens.end())
        current = nullptr;
}

Token* MacroExpander::next() {
    Token* result = (*current)->clone(alloc);
    current++;
    if (current == tokens.end())
        current = nullptr;

    return result;
}

bool MacroExpander::done() const {
    return current == nullptr;
}

void MacroExpander::expand(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs) {
    if (!macro->formalArguments) {
        // simple macro; just take body tokens
        tokens.appendRange(macro->body);
        return;
    }
}

}