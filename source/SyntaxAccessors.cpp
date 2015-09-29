#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "Debug.h"
#include "Buffer.h"
#include "StringRef.h"
#include "Token.h"
#include "SyntaxNode.h"
#include "AllSyntax.h"

namespace slang {

TokenOrSyntax DirectiveSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return directive;
        case 1: return endOfDirective;
        default: return nullptr;
    }
}

TokenOrSyntax IncludeDirectiveSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return directive;
        case 1: return fileName;
        case 2: return endOfDirective;
        default: return nullptr;
    }
}

TokenOrSyntax DefineDirectiveSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return directive;
        case 1: return name;
        case 2: return formalArguments;
        case 3: return &body;
        case 4: return endOfDirective;
        default: return nullptr;
    }
}

TokenOrSyntax MacroArgumentDefaultSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return equals;
        case 1: return &tokens;
        default: return nullptr;
    }
}

TokenOrSyntax MacroFormalArgumentSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return name;
        case 1: return defaultValue;
        default: return nullptr;
    }
}

TokenOrSyntax MacroFormalArgumentListSyntax::getChild(uint32_t index) const {
    switch (index) {
        case 0: return openParen;
        case 1: return &args;
        case 2: return closeParen;
        default: return nullptr;
    }
}

}