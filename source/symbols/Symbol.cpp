//------------------------------------------------------------------------------
// Symbol.cpp
// Symbols for semantic analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/Symbol.h"

#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/types/Type.h"
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

} // namespace

namespace slang {

bool Symbol::isType() const {
    return Type::isKind(kind);
}

bool Symbol::isValue() const {
    return ValueSymbol::isKind(kind);
}

const DeclaredType* Symbol::getDeclaredType() const {
    switch (kind) {
        case SymbolKind::TypeAlias:
            return &as<TypeAliasType>().targetType;
        case SymbolKind::Subroutine:
            return &as<SubroutineSymbol>().declaredReturnType;
        case SymbolKind::MethodPrototype:
            return &as<MethodPrototypeSymbol>().declaredReturnType;
        case SymbolKind::NetType:
            return &as<NetType>().declaredType;
        case SymbolKind::TypeParameter:
            return &as<TypeParameterSymbol>().targetType;
        case SymbolKind::AssertionPort:
            return &as<AssertionPortSymbol>().declaredType;
        case SymbolKind::RandSeqProduction:
            return &as<RandSeqProductionSymbol>().declaredReturnType;
        default:
            if (isValue())
                return as<ValueSymbol>().getDeclaredType();
            return nullptr;
    }
}

static void getHierarchicalPathImpl(const Symbol& symbol, std::string& buffer) {
    auto scope = symbol.getParentScope();
    auto current = &symbol;
    if (scope && symbol.kind == SymbolKind::InstanceBody) {
        auto parents = scope->getCompilation().getParentInstances(symbol.as<InstanceBodySymbol>());
        if (parents.empty())
            return;

        current = parents[0];
        scope = current->getParentScope();
    }

    if (scope) {
        auto& parent = scope->asSymbol();
        if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
            getHierarchicalPathImpl(parent, buffer);

            if (!current->name.empty()) {
                if (parent.kind == SymbolKind::Package || parent.kind == SymbolKind::ClassType)
                    buffer.append("::");
                else
                    buffer.append(".");
            }
        }
    }

    if (!current->name.empty())
        buffer.append(current->name);
}

void Symbol::getHierarchicalPath(std::string& buffer) const {
    size_t sz = buffer.size();
    getHierarchicalPathImpl(*this, buffer);

    if (sz == buffer.size())
        buffer.append("$unit");
}

static void getLexicalPathImpl(const Symbol& symbol, std::string& buffer) {
    if (symbol.getParentScope()) {
        auto& parent = symbol.getParentScope()->asSymbol();
        if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
            getLexicalPathImpl(parent, buffer);

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

void Symbol::getLexicalPath(std::string& buffer) const {
    getLexicalPathImpl(*this, buffer);
}

optional<bool> Symbol::isDeclaredBefore(const Symbol& target) const {
    return isDeclaredBefore(LookupLocation::before(target));
}

optional<bool> Symbol::isDeclaredBefore(LookupLocation target) const {
    LookupLocation ll = LookupLocation::before(*this);
    if (!target.getScope())
        return ll < target;

    // Find a common parent scope for the two symbols. Start with our parent and
    // walk upwards until we find `target`s scope or run into a compilation unit.
    SmallMap<const Scope*, LookupLocation, 8> locMap;
    const Symbol* sym = this;
    const Scope* scope = ll.getScope();

    while (sym->kind != SymbolKind::CompilationUnit && scope && scope != target.getScope()) {
        locMap[scope] = ll;
        sym = &scope->asSymbol();
        ll = LookupLocation::before(*sym);
        scope = ll.getScope();
    }

    if (scope == target.getScope())
        return ll < target;

    // If target wasn't in a direct scope of any of our own parents,
    // repeat the process walking up target's scopes.
    sym = &target.getScope()->asSymbol();
    ll = LookupLocation::before(*sym);

    while ((scope = ll.getScope()) != nullptr && sym->kind != SymbolKind::CompilationUnit) {
        if (auto it = locMap.find(scope); it != locMap.end())
            return it->second < ll;

        sym = &scope->asSymbol();
        ll = LookupLocation::before(*sym);
    }

    return std::nullopt;
}

const Definition* Symbol::getDeclaringDefinition() const {
    auto curr = this;
    while (curr->kind != SymbolKind::InstanceBody) {
        auto scope = curr->getParentScope();
        if (!scope)
            return nullptr;

        curr = &scope->asSymbol();
    }

    return &curr->as<InstanceBodySymbol>().getDefinition();
}

RandMode Symbol::getRandMode() const {
    switch (kind) {
        case SymbolKind::ClassProperty:
            return as<ClassPropertySymbol>().randMode;
        case SymbolKind::Field:
            return as<FieldSymbol>().randMode;
        default:
            return RandMode::None;
    }
}

void Symbol::setAttributes(const Scope& scope, span<const AttributeInstanceSyntax* const> syntax) {
    if (syntax.empty())
        return;

    scope.getCompilation().setAttributes(*this, AttributeSymbol::fromSyntax(syntax, scope, *this));
}

const Scope* Symbol::scopeOrNull() const {
    AsScopeVisitor visitor;
    return visit(visitor);
}

} // namespace slang
