//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/Symbol.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/text/SourceManager.h"

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
                    // TODO: ?
                    // member.visit(*this, j);
                }
            }
        }
    }
};

} // namespace

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

const DeclaredType* Symbol::getDeclaredType() const {
    switch (kind) {
        case SymbolKind::TypeAlias:
            return &as<TypeAliasType>().targetType;
        case SymbolKind::Subroutine:
            return &as<SubroutineSymbol>().declaredReturnType;
        default:
            if (isValue())
                return as<ValueSymbol>().getDeclaredType();
            return nullptr;
    }
}

const Scope* Symbol::scopeOrNull() const {
    AsScopeVisitor visitor;
    return visit(visitor);
}

ValueSymbol::ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                         bitmask<DeclaredTypeFlags> flags) :
    Symbol(kind, name, location),
    declaredType(*this, flags) {
}

bool ValueSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Net:
        case SymbolKind::EnumValue:
        case SymbolKind::Parameter:
        case SymbolKind::Port:
            return true;
        default:
            return VariableSymbol::isKind(kind);
    }
}

void to_json(json& j, const Symbol& symbol) {
    ToJsonVisitor visitor;
    symbol.visit(visitor, j);
}

} // namespace slang
