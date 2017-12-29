//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "text/SourceManager.h"

namespace slang {

const Symbol* Symbol::findAncestor(SymbolKind searchKind) const {
    const Symbol* current = this;
    while (current->kind != searchKind) {
        if (current->kind == SymbolKind::Root)
            return nullptr;

        current = &current->getScope()->asSymbol();
    }
    return current;
}

Diagnostic& Symbol::addError(DiagCode code, SourceLocation location_) const {
    return getScope()->getCompilation().addError(code, location_);
}

}
