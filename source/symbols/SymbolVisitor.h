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
    template<typename T>
    void visit(const T& symbol) {
        if constexpr (std::is_base_of_v<Scope, T>()) {
            visitScope(*static_cast<const Scope*>(&symbol));
        }
    }

    void visitScope(const Scope& scope) {
        for (auto member : scope.members())
            member->visit(*static_cast<TDerived*>(this));
    }
};

template<typename TVisitor, typename... Args>
decltype(auto) Symbol::visit(TVisitor& visitor, Args&&... args) const {
#define CASE1(k) case SymbolKind::k: return visitor.visit(*static_cast<const k##Symbol*>(this), std::forward<Args>(args)...)
#define CASE2(k) case SymbolKind::k: return visitor.visit(*static_cast<const k*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case SymbolKind::Unknown: return visitor.visit(*this, std::forward<Args>(args)...);
        CASE1(Root);
        CASE1(CompilationUnit);
        CASE1(TransparentMember);
        CASE2(BuiltInIntegerType);
        CASE2(VectorType);
        CASE2(FloatingType);
        CASE2(EnumType);
        CASE1(EnumValue);
        CASE2(PackedArrayType);
        CASE2(PackedStructType);
        CASE2(UnpackedStructType);
        CASE2(VoidType);
        CASE2(NullType);
        CASE2(CHandleType);
        CASE2(StringType);
        CASE2(EventType);
        CASE2(ErrorType);
        CASE1(Parameter);
        CASE1(ModuleInstance);
        CASE1(Package);
        CASE1(ExplicitImport);
        CASE1(WildcardImport);
        CASE1(GenerateBlock);
        CASE1(GenerateBlockArray);
        CASE1(ProceduralBlock);
        CASE1(SequentialBlock);
        CASE1(Variable);
        CASE1(Instance);
        CASE1(FormalArgument);
        CASE1(Subroutine);

        case SymbolKind::TypeAlias: THROW_UNREACHABLE;
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
#undef CASE2
#undef CASE1
    THROW_UNREACHABLE;
}

}