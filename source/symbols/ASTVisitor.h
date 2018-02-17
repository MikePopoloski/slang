//------------------------------------------------------------------------------
// ASTVisitor.h
// AST traversal.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/Statements.h"

#include "HierarchySymbols.h"
#include "MemberSymbols.h"
#include "TypeSymbols.h"

namespace slang {

/// Use this type as a base class for AST visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class ASTVisitor {
public:
#define DERIVED *static_cast<TDerived*>(this)
    template<typename T>
    void visit(const T& t) {
        if constexpr (has_handler<T>::value)
            static_cast<TDerived*>(this)->handle(t);
        else
            visitDefault(t);
    }

    void visitDefault(const Symbol&) {}
    void visitDefault(const Statement&) {}
    void visitDefault(const Expression&) {}

    template<typename T>
    typename std::enable_if_t<std::is_base_of_v<Scope, T>> visitDefault(const T& symbol) {
        for (const auto& member : symbol.members())
            member.visit(DERIVED);

        if constexpr (std::is_base_of_v<StatementBodiedScope, T>) {
            auto body = symbol.getBody();
            if (body)
                body->visit(DERIVED);
        }
    }

#undef DERIVED

    struct tag;
    tag handle(...);

private:
    template<typename A, typename B>
    struct is_different : std::integral_constant<bool, !std::is_same<A, B>::value> {};

    template<typename T>
    using has_handler = is_different<tag, decltype(std::declval<TDerived>().handle(std::declval<T>()))>;
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

template<typename TVisitor, typename... Args>
decltype(auto) Statement::visit(TVisitor& visitor, Args&&... args) const {
#define CASE(k, n) case StatementKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case StatementKind::Invalid: return visitor.visit(*this, std::forward<Args>(args)...);
        CASE(List, StatementList);
        CASE(SequentialBlock, SequentialBlockStatement);
        CASE(ExpressionStatement, ExpressionStatement);
        CASE(VariableDeclaration, VariableDeclStatement);
        CASE(Return, ReturnStatement);
        CASE(Conditional, ConditionalStatement);
        CASE(ForLoop, ForLoopStatement);
    }
#undef CASE
    THROW_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Expression::visit(TVisitor& visitor, Args&&... args) const {
#define CASE(k, n) case ExpressionKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case ExpressionKind::Invalid: return visitor.visit(*this, std::forward<Args>(args)...);
        CASE(IntegerLiteral, IntegerLiteral);
        CASE(RealLiteral, RealLiteral);
        CASE(UnbasedUnsizedIntegerLiteral, UnbasedUnsizedIntegerLiteral);
        CASE(NamedValue, NamedValueExpression);
        CASE(UnaryOp, UnaryExpression);
        CASE(BinaryOp, BinaryExpression);
        CASE(ConditionalOp, ConditionalExpression);
        CASE(Concatenation, ConcatenationExpression);
        CASE(ElementSelect, ElementSelectExpression);
        CASE(RangeSelect, RangeSelectExpression);
        CASE(Call, CallExpression);
        CASE(Conversion, ConversionExpression);
    }
#undef CASE
    THROW_UNREACHABLE;
}

}