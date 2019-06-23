//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/Symbol.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
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
        if constexpr (std::is_base_of_v<Type, T> && !std::is_same_v<TypeAliasType, T>) {
            j = symbol.toString();
        }
        else {
            j["name"] = std::string(symbol.name);
            j["kind"] = toString(symbol.kind);
            j["addr"] = uintptr_t(&symbol);

            auto scope = symbol.getScope();
            if (scope) {
                for (auto attr : scope->getCompilation().getAttributes(symbol))
                    j["attributes"].push_back(*attr);
            }

            if constexpr (std::is_base_of_v<ValueSymbol, T>) {
                j["type"] = symbol.getType();

                auto& value = symbol.getConstantValue();
                if (value)
                    j["value"] = value;

                if (auto init = symbol.getInitializer())
                    j["initializer"] = *init;
            }

            if constexpr (std::is_base_of_v<Scope, T>) {
                for (const auto& member : symbol.members())
                    j["members"].push_back(member);
            }

            if constexpr (!std::is_same_v<Symbol, T>) {
                symbol.toJson(j);
            }
        }
    }
};

} // namespace

namespace slang {

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
        case SymbolKind::NetType:
            return &as<NetType>().declaredType;
        default:
            if (isValue())
                return as<ValueSymbol>().getDeclaredType();
            return nullptr;
    }
}

void Symbol::getHierarchicalPath(std::string& buffer) const {
    if (parentScope) {
        auto& parent = parentScope->asSymbol();
        parent.getHierarchicalPath(buffer);

        if (parent.kind == SymbolKind::Package || parent.kind == SymbolKind::ClassType)
            buffer.append("::");
        else
            buffer.append(".");
    }

    if (name.empty())
        buffer.append("<unnamed>");
    else
        buffer.append(name);
}

const Scope* Symbol::scopeOrNull() const {
    AsScopeVisitor visitor;
    return visit(visitor);
}

std::string Symbol::jsonLink(const Symbol& target) {
    return std::to_string(uintptr_t(&target)) + " " +
           (target.isType() ? target.as<Type>().toString() : std::string(target.name));
}

void AttributeSymbol::toJson(json& j) const {
    j["value"] = value;
}

ValueSymbol::ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                         bitmask<DeclaredTypeFlags> flags) :
    Symbol(kind, name, location),
    declaredType(*this, flags) {
}

void ValueSymbol::setFromDeclarator(const DeclaratorSyntax& decl) {
    declaredType.setFromDeclarator(decl);
    setSyntax(decl);
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
