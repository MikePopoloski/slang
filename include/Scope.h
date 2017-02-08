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
    Scope();

    bool add(const Symbol* symbol);

    template<typename TContainer>
    bool addRange(const TContainer& container) {
        for (const auto& symbol : container)
            if (!add(symbol)) return false;
        return true;
    }

    const Symbol* lookup(StringRef name, bool local = false) const;

    const Symbol* getNth(const SymbolKind& kind, size_t index) const;

    const Scope* parent() const { return parentScope; }

    static const Scope* const Empty;

    std::string toString() const;

private:
    std::unordered_map<StringRef, const Symbol*> table;
    std::vector<const Symbol*> list;
    const Scope* parentScope;
};

}
