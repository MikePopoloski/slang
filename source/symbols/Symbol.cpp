//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "json.hpp"

#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "symbols/HierarchySymbols.h"
#include "symbols/MemberSymbols.h"
#include "symbols/ASTVisitor.h"
#include "symbols/TypeSymbols.h"
#include "text/SourceManager.h"

namespace {

using namespace slang;

struct AsScopeVisitor {
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

struct ToJsonVisitor {
    template<typename T>
    void visit(const T& symbol, json& j) {
        if constexpr (std::is_base_of_v<Type, T>) {
            j = symbol.toString();
        }
        else {
            j["name"] = std::string(symbol.name);
            j["kind"] = symbol.kind;
            if constexpr (!std::is_same_v<Symbol, T>) {
                symbol.toJson(j);
            }

            if constexpr (std::is_base_of_v<Scope, T>) {
                j["members"] = json::array();
                for (const auto& member : symbol.members()) {
                    j["members"].push_back(member);
                    //member.visit(*this, j);
                }
            }
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
    AsScopeVisitor visitor;
    return visit(visitor);
}

const Type& ValueSymbol::getType() const {
    switch (kind) {
        case SymbolKind::EnumValue:
            return as<EnumValueSymbol>().type;
        case SymbolKind::Parameter:
            return as<ParameterSymbol>().getType();
        case SymbolKind::Net:
            return *as<NetSymbol>().dataType;
        default:
            return *as<VariableSymbol>().type;
    }
}

bool ValueSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Net:
        case SymbolKind::EnumValue:
        case SymbolKind::Parameter:
            return true;
        default:
            return VariableSymbol::isKind(kind);
    }
}

void to_json(json& j, const Symbol& symbol) {
    ToJsonVisitor visitor;
    symbol.visit(visitor, j);
}

}
