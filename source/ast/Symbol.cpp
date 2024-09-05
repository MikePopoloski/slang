//------------------------------------------------------------------------------
// Symbol.cpp
// Symbols for semantic analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Symbol.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/text/CharInfo.h"
#include "slang/text/FormatBuffer.h"

namespace {

using namespace slang;
using namespace slang::ast;

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

namespace slang::ast {

using namespace syntax;

const Scope* Symbol::getHierarchicalParent() const {
    if (kind == SymbolKind::InstanceBody) {
        auto parentInst = as<InstanceBodySymbol>().parentInstance;
        SLANG_ASSERT(parentInst);
        return parentInst->getParentScope();
    }
    else if (kind == SymbolKind::CheckerInstanceBody) {
        auto parentInst = as<CheckerInstanceBodySymbol>().parentInstance;
        SLANG_ASSERT(parentInst);
        return parentInst->getParentScope();
    }
    return parentScope;
}

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
        case SymbolKind::Coverpoint:
            return &as<CoverpointSymbol>().declaredType;
        default:
            if (isValue())
                return as<ValueSymbol>().getDeclaredType();
            return nullptr;
    }
}

static void getHierarchicalPathImpl(const Symbol& symbol, FormatBuffer& buffer) {
    auto scope = symbol.getParentScope();
    auto current = &symbol;
    if (scope && symbol.kind == SymbolKind::InstanceBody) {
        current = symbol.as<InstanceBodySymbol>().parentInstance;
        SLANG_ASSERT(current);

        scope = current->getParentScope();
    }
    else if (scope && symbol.kind == SymbolKind::CheckerInstanceBody) {
        current = symbol.as<CheckerInstanceBodySymbol>().parentInstance;
        SLANG_ASSERT(current);

        scope = current->getParentScope();
    }

    std::string_view separator;
    if (scope) {
        auto& parent = scope->asSymbol();
        if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
            getHierarchicalPathImpl(parent, buffer);
            if (parent.kind == SymbolKind::Package || parent.kind == SymbolKind::ClassType ||
                parent.kind == SymbolKind::CovergroupType) {
                separator = "::"sv;
            }
            else {
                separator = "."sv;
            }
        }
    }

    auto needsEscaping = [](std::string_view text) {
        if (!text.empty()) {
            if (!isValidCIdChar(text[0]) || isDecimalDigit(text[0]))
                return true;

            for (size_t i = 1; i < text.length(); i++) {
                if (!isValidCIdChar(text[i]) && text[i] != '$')
                    return true;
            }
        }
        return false;
    };

    auto addName = [&](std::string_view text) {
        if (!separator.empty())
            buffer.append(separator);

        // If the name requires escaping add that here.
        if (needsEscaping(text))
            buffer.format("\\{} ", text);
        else
            buffer.append(text);
    };

    if (!current->name.empty())
        addName(current->name);

    if (current->kind == SymbolKind::GenerateBlockArray) {
        auto& array = current->as<GenerateBlockArraySymbol>();
        if (current->name.empty())
            addName(array.getExternalName());
    }
    else if (current->kind == SymbolKind::GenerateBlock) {
        auto& block = current->as<GenerateBlockSymbol>();
        if (auto index = block.arrayIndex) {
            buffer.append("[");
            buffer.append(index->toString(LiteralBase::Decimal, false));
            buffer.append("]");
        }
        else if (current->name.empty()) {
            addName(block.getExternalName());
        }
    }
    else if (current->kind == SymbolKind::Instance ||
             current->kind == SymbolKind::CheckerInstance) {
        auto& inst = current->as<InstanceSymbolBase>();
        if (!inst.arrayPath.empty()) {
            SmallVector<ConstantRange, 8> instanceDimVec;
            inst.getArrayDimensions(instanceDimVec);

            std::span<const ConstantRange> instanceDims = instanceDimVec;
            std::span<const int32_t> arrayPath = inst.arrayPath;
            SLANG_ASSERT(instanceDims.size() == arrayPath.size());

            for (size_t i = 0; i < instanceDims.size(); i++) {
                auto dim = instanceDims[i];
                auto idx = dim.translateIndex(arrayPath[i]);
                idx += dim.lower();

                buffer.format("[{}]", idx);
            }
        }
    }
}

void Symbol::getHierarchicalPath(std::string& result) const {
    FormatBuffer buffer;
    getHierarchicalPathImpl(*this, buffer);
    if (buffer.empty())
        buffer.append("$unit");

    result.append(buffer.data(), buffer.size());
}

static void getLexicalPathImpl(const Symbol& symbol, std::string& buffer) {
    if (symbol.getParentScope()) {
        auto& parent = symbol.getParentScope()->asSymbol();
        if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
            getLexicalPathImpl(parent, buffer);

            if (!symbol.name.empty()) {
                if (parent.kind == SymbolKind::Package || parent.kind == SymbolKind::ClassType ||
                    parent.kind == SymbolKind::CovergroupType) {
                    buffer.append("::");
                }
                else {
                    buffer.append(".");
                }
            }
        }
    }

    if (!symbol.name.empty())
        buffer.append(symbol.name);
}

void Symbol::getLexicalPath(std::string& buffer) const {
    getLexicalPathImpl(*this, buffer);
}

std::optional<bool> Symbol::isDeclaredBefore(const Symbol& target) const {
    return isDeclaredBefore(LookupLocation::after(target));
}

std::optional<bool> Symbol::isDeclaredBefore(LookupLocation target) const {
    LookupLocation ll = LookupLocation::before(*this);
    if (!target.getScope())
        return ll < target;

    // Walk up the target's tree until we find our own scope.
    while (target.getScope() != ll.getScope()) {
        auto& sym = target.getScope()->asSymbol();
        target = LookupLocation::after(sym);
        if (sym.kind == SymbolKind::CompilationUnit || !target.getScope())
            return std::nullopt;
    }

    return ll < target;
}

const DefinitionSymbol* Symbol::getDeclaringDefinition() const {
    auto curr = this;
    while (curr->kind != SymbolKind::InstanceBody) {
        auto scope = curr->getParentScope();
        if (!scope)
            return nullptr;

        curr = &scope->asSymbol();
    }

    return &curr->as<InstanceBodySymbol>().getDefinition();
}

const SourceLibrary* Symbol::getSourceLibrary() const {
    auto curr = this;
    while (true) {
        switch (curr->kind) {
            case SymbolKind::Definition:
                return &curr->as<DefinitionSymbol>().sourceLibrary;
            case SymbolKind::CompilationUnit:
                return &curr->as<CompilationUnitSymbol>().sourceLibrary;
            case SymbolKind::InstanceBody:
                return &curr->as<InstanceBodySymbol>().getDefinition().sourceLibrary;
            case SymbolKind::Instance:
                return &curr->as<InstanceSymbol>().getDefinition().sourceLibrary;
            default:
                auto scope = curr->getParentScope();
                if (!scope)
                    return nullptr;

                curr = &scope->asSymbol();
                break;
        }
    }
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

void Symbol::setAttributes(const Scope& scope,
                           std::span<const AttributeInstanceSyntax* const> syntax) {
    if (syntax.empty())
        return;

    scope.getCompilation().setAttributes(*this, AttributeSymbol::fromSyntax(syntax, scope, *this));
}

const Scope* Symbol::scopeOrNull() const {
    AsScopeVisitor visitor;
    return visit(visitor);
}

} // namespace slang::ast
