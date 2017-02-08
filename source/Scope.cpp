#include "Scope.h"
#include "Symbol.h"

namespace slang {

static const Scope emptyScope;
const Scope *const Scope::Empty = &emptyScope;

Scope::Scope() : parentScope{Scope::Empty} {}

bool Scope::add(const Symbol *symbol) {
        ASSERT(symbol);
    list.emplace_back(symbol);
    return table.emplace(symbol->name, symbol).second;
}

const Symbol *Scope::lookup(StringRef name, bool local) const {
    for (auto scope = this; scope != Scope::Empty; scope = scope->parent()) {
        auto it = table.find(name);
        if (it != table.end()) return it->second;
        if (local) return nullptr;
    }
    return nullptr;
}

const Symbol* Scope::getNth(const SymbolKind& kind, size_t index) const {
    for (const Symbol* s : list) {
        if (s->kind == kind ) {
            if (index == 0)
                return s;
            index--;
        }
    }
    return nullptr;
}

}
