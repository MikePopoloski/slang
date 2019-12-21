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
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/util/StackContainer.h"

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

            auto scope = symbol.getParentScope();
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

const Scope* Symbol::getLexicalScope() const {
    if (InstanceSymbol::isKind(kind))
        return as<InstanceSymbol>().definition.getParentScope();
    else
        return getParentScope();
}

const DeclaredType* Symbol::getDeclaredType() const {
    switch (kind) {
        case SymbolKind::TypeAlias:
            return &as<TypeAliasType>().targetType;
        case SymbolKind::Subroutine:
            return &as<SubroutineSymbol>().declaredReturnType;
        case SymbolKind::NetType:
            return &as<NetType>().declaredType;
        case SymbolKind::TypeParameter:
            return &as<TypeParameterSymbol>().targetType;
        default:
            if (isValue())
                return as<ValueSymbol>().getDeclaredType();
            return nullptr;
    }
}

static void getHierarchicalPathImpl(const Symbol& symbol, std::string& buffer) {
    if (symbol.getParentScope()) {
        auto& parent = symbol.getParentScope()->asSymbol();
        if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
            getHierarchicalPathImpl(parent, buffer);

            if (!symbol.name.empty()) {
                if (parent.kind == SymbolKind::Package || parent.kind == SymbolKind::ClassType)
                    buffer.append("::");
                else
                    buffer.append(".");
            }
        }
    }

    if (!symbol.name.empty())
        buffer.append(symbol.name);
}

void Symbol::getHierarchicalPath(std::string& buffer) const {
    size_t sz = buffer.size();
    getHierarchicalPathImpl(*this, buffer);

    if (sz == buffer.size())
        buffer.append("$unit");
}

optional<bool> Symbol::isBeforeInCompilationUnit(const Symbol& target) const {
    // Find a common parent scope for the two symbols. Start with our parent and
    // walk upwards until we find `target`s scope or run into a compilation unit.
    SmallMap<const Scope*, LookupLocation, 8> locMap;
    const Symbol* sym = this;
    const Scope* scope;
    while ((scope = sym->getLexicalScope()) != nullptr &&
           sym->kind != SymbolKind::CompilationUnit && scope != target.getLexicalScope()) {
        locMap[scope] = LookupLocation::beforeLexical(*sym);
        sym = &scope->asSymbol();
    }

    if (scope == target.getLexicalScope())
        return LookupLocation::beforeLexical(*sym) < LookupLocation::beforeLexical(target);

    // If `target` wasn't in a direct scope of any of our own parents,
    // repeat the process walking up `target`s scopes.
    sym = &target;
    while ((scope = sym->getLexicalScope()) != nullptr &&
           sym->kind != SymbolKind::CompilationUnit) {
        if (auto it = locMap.find(scope); it != locMap.end())
            return it->second < LookupLocation::beforeLexical(*sym);

        sym = &scope->asSymbol();
    }

    return std::nullopt;
}

const Scope* Symbol::scopeOrNull() const {
    AsScopeVisitor visitor;
    return visit(visitor);
}

std::string Symbol::jsonLink(const Symbol& target) {
    return std::to_string(uintptr_t(&target)) + " " +
           (target.isType() ? target.as<Type>().toString() : std::string(target.name));
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
