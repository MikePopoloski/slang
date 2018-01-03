//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "symbols/HierarchySymbols.h"
#include "symbols/MemberSymbols.h"
#include "symbols/SymbolVisitor.h"
#include "symbols/TypeSymbols.h"
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

bool Symbol::isType() const {
    return Type::isKind(kind);
}

bool Symbol::isValue() const {
    return ValueSymbol::isKind(kind);
}

bool Symbol::isInstance() const {
    return InstanceSymbol::isKind(kind);
}

const Scope* Symbol::scopeOrNull() const {
    Visitor visitor;
    return visit(visitor);
}

const Type& ValueSymbol::getType() const {
    switch (kind) {
        case SymbolKind::EnumValue:
            return as<EnumValueSymbol>().type;
        case SymbolKind::Variable:
        case SymbolKind::FormalArgument:
            return *as<VariableSymbol>().type;
        case SymbolKind::Parameter:
            return as<ParameterSymbol>().getType();
        default:
            THROW_UNREACHABLE;
    }
}

bool ValueSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::EnumValue:
        case SymbolKind::Variable:
        case SymbolKind::FormalArgument:
        case SymbolKind::Parameter:
            return true;
        default:
            return false;
    }
}

}
