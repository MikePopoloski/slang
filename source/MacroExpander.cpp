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

    // match up actual arguments with formal parameters
    ASSERT(actualArgs);
    auto& formalList = macro->formalArguments->args;
    auto& actualList = actualArgs->args;
    if (actualList.count() > formalList.count()) {
        // TODO: error
    }

    argumentMap.clear();
    for (int i = 0; i < formalList.count(); i++) {
        auto formal = formalList[i];
        auto name = formal->name->valueText();

        const TokenList* tokenList = nullptr;
        if (actualList.count() > i) {
            // if our actual argument is empty and we have a default, take that
            tokenList = &actualList[i]->tokens;
            if (tokenList->count() == 0 && formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
        }
        else {
            // if we've run out of actual args make sure we have a default for this one
            if (formal->defaultValue)
                tokenList = &formal->defaultValue->tokens;
            else {
                // TODO: error
            }
        }
        argumentMap[name] = tokenList;
    }

    // now add each body token, substituting arguments as necessary
    for (auto& token : macro->body) {
        if (token->kind != TokenKind::Identifier)
            tokens.append(token);
        else {
            // check for formal param
            auto it = argumentMap.find(token->valueText());
            if (it == argumentMap.end())
                tokens.append(token);
            else
                tokens.appendRange(*it->second);
        }
    }
}

}