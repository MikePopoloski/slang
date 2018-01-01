//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "symbols/SymbolVisitor.h"
#include "text/SourceManager.h"

namespace {

using namespace slang;

struct Visitor {
    template<typename T>
    const Scope* visit(const T& symbol) {
        if constexpr (std::is_base_of_v<Scope, T>) {
            return static_cast<const Scope*>(&symbol);
        }
        else {
            (void)symbol;
            return nullptr;
        }
    }
};

}

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

const Scope* Symbol::scopeOrNull() const {
    Visitor visitor;
    return visit(visitor);
}

}
