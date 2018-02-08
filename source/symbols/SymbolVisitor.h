//------------------------------------------------------------------------------
// SymbolVisitor.h
// Symbol tree traversal.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "HierarchySymbols.h"
#include "MemberSymbols.h"
#include "TypeSymbols.h"

namespace slang {

/// Use this type as a base class for symbol visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class SymbolVisitor {
public:
    void visit(const Symbol&) {}

    template<typename T>
    typename std::enable_if_t<std::is_base_of_v<Scope, T>> visit(const T& symbol) {
        visitScope(*static_cast<const Scope*>(&symbol));
    }

    void visitScope(const Scope& scope) {
        for (const auto& member : scope.members())
            member.visit(*static_cast<TDerived*>(this));
    }
};

template<typename TVisitor, typename... Args>
decltype(auto) Symbol::visit(TVisitor& visitor, Args&&... args) const {
#define SYMBOL(k) case SymbolKind::k: return visitor.visit(*static_cast<const k##Symbol*>(this), std::forward<Args>(args)...)
#define TYPE(k) case SymbolKind::k: return visitor.visit(*static_cast<const k*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case SymbolKind::Unknown: return visitor.visit(*this, std::forward<Args>(args)...);
        case SymbolKind::TypeAlias: return visitor.visit(*static_cast<const TypeAliasType*>(this), std::forward<Args>(args)...);
        SYMBOL(Root);
        SYMBOL(CompilationUnit);
        SYMBOL(TransparentMember);
        SYMBOL(EnumValue);
        SYMBOL(ForwardingTypedef);
        SYMBOL(Parameter);
        SYMBOL(ModuleInstance);
        SYMBOL(Package);
        SYMBOL(ExplicitImport);
        SYMBOL(WildcardImport);
        SYMBOL(GenerateBlock);
        SYMBOL(GenerateBlockArray);
        SYMBOL(ProceduralBlock);
        SYMBOL(SequentialBlock);
        SYMBOL(Variable);
        SYMBOL(FormalArgument);
        SYMBOL(Subroutine);
        TYPE(PredefinedIntegerType);
        TYPE(ScalarType);
        TYPE(FloatingType);
        TYPE(EnumType);
        TYPE(PackedArrayType);
        TYPE(PackedStructType);
        TYPE(UnpackedStructType);
        TYPE(VoidType);
        TYPE(NullType);
        TYPE(CHandleType);
        TYPE(StringType);
        TYPE(EventType);
        TYPE(ErrorType);
            
        case SymbolKind::UnpackedArrayType: THROW_UNREACHABLE;
        case SymbolKind::PackedUnionType: THROW_UNREACHABLE;
        case SymbolKind::UnpackedUnionType: THROW_UNREACHABLE;
        case SymbolKind::ClassType: THROW_UNREACHABLE;
        case SymbolKind::Modport: THROW_UNREACHABLE;
        case SymbolKind::InterfaceInstance: THROW_UNREACHABLE;
        case SymbolKind::Program: THROW_UNREACHABLE;
        case SymbolKind::Attribute: THROW_UNREACHABLE;
        case SymbolKind::Genvar: THROW_UNREACHABLE;
    }
#undef TYPE
#undef SYMBOL
    THROW_UNREACHABLE;
}

}