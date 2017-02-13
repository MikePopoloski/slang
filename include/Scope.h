#pragma once

#include <vector>
#include <unordered_map>

#include "StringRef.h"

namespace slang {

class Symbol;
enum class SymbolKind;

// Maintains context (like in a specific scope) and knows about parent
// contexts so that symbol lookup can be performed.
class Scope {
public:
    Scope() {}
    explicit Scope(const Scope* parent) : parents(1, parent) {}

    bool add(const Symbol* symbol);

    template<typename TContainer>
    bool addRange(const TContainer& container) {
        for (const auto& symbol : container)
            if (lookup(symbol->name, true)) return false;
        for (const auto& symbol : container)
            add(symbol);
        return true;
    }

    const Symbol* lookup(StringRef name, bool local = false) const;

    const Symbol* getNth(const SymbolKind& kind, size_t index) const;

    static const Scope* const Empty;

    std::string toString() const;

    void addParentScope(const Scope* scope) { parents.emplace_back(scope); }

private:
    std::unordered_map<StringRef, const Symbol*> table;
    std::vector<const Symbol*> list;
    std::vector<const Scope*> parents;
};

}
