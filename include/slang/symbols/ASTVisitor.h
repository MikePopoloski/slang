//------------------------------------------------------------------------------
// ASTVisitor.h
// AST traversal.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expressions.h"
#include "slang/binding/Statements.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/TypeSymbols.h"

namespace slang {

/// Use this type as a base class for AST visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class ASTVisitor {
    HAS_METHOD_TRAIT(handle);

public:
#define DERIVED *static_cast<TDerived*>(this)
    template<typename T>
    void visit(const T& t) {
        if constexpr (has_handle_v<TDerived, void, T>)
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
};

template<typename TVisitor, typename... Args>
decltype(auto) Symbol::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define SYMBOL(k) case SymbolKind::k: return visitor.visit(*static_cast<const k##Symbol*>(this), std::forward<Args>(args)...)
#define TYPE(k) case SymbolKind::k: return visitor.visit(*static_cast<const k*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case SymbolKind::Unknown: return visitor.visit(*this, std::forward<Args>(args)...);
        case SymbolKind::DeferredMember: return visitor.visit(*this, std::forward<Args>(args)...);
        case SymbolKind::TypeAlias: return visitor.visit(*static_cast<const TypeAliasType*>(this), std::forward<Args>(args)...);
        SYMBOL(Root);
        SYMBOL(CompilationUnit);
        SYMBOL(TransparentMember);
        SYMBOL(EnumValue);
        SYMBOL(ForwardingTypedef);
        SYMBOL(Parameter);
        SYMBOL(Port);
        SYMBOL(InterfacePort);
        SYMBOL(Definition);
        SYMBOL(ModuleInstance);
        SYMBOL(InterfaceInstance);
        SYMBOL(InstanceArray);
        SYMBOL(Package);
        SYMBOL(ExplicitImport);
        SYMBOL(WildcardImport);
        SYMBOL(GenerateBlock);
        SYMBOL(GenerateBlockArray);
        SYMBOL(ProceduralBlock);
        SYMBOL(SequentialBlock);
        SYMBOL(Net);
        SYMBOL(Variable);
        SYMBOL(FormalArgument);
        SYMBOL(Field);
        SYMBOL(Subroutine);
        SYMBOL(Modport);
        SYMBOL(ContinuousAssign);
        TYPE(PredefinedIntegerType);
        TYPE(ScalarType);
        TYPE(FloatingType);
        TYPE(EnumType);
        TYPE(PackedArrayType);
        TYPE(UnpackedArrayType);
        TYPE(PackedStructType);
        TYPE(UnpackedStructType);
        TYPE(VoidType);
        TYPE(NullType);
        TYPE(CHandleType);
        TYPE(StringType);
        TYPE(EventType);
        TYPE(ErrorType);
        TYPE(NetType);

        case SymbolKind::PackedUnionType: THROW_UNREACHABLE;
        case SymbolKind::UnpackedUnionType: THROW_UNREACHABLE;
        case SymbolKind::ClassType: THROW_UNREACHABLE;
        case SymbolKind::Program: THROW_UNREACHABLE;
        case SymbolKind::Attribute: THROW_UNREACHABLE;
        case SymbolKind::Genvar: THROW_UNREACHABLE;
    }
#undef TYPE
#undef SYMBOL
    // clang-format on
    THROW_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Statement::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
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
    // clang-format on
    THROW_UNREACHABLE;
}

namespace detail {

template<typename TExpression, typename TVisitor, typename... Args>
decltype(auto) visitExpression(TExpression* expr, TVisitor& visitor, Args&&... args) {
    // clang-format off
#define CASE(k, n) case ExpressionKind::k: return visitor.visit(\
                        *static_cast<std::conditional_t<std::is_const_v<TExpression>, const n*, n*>>(expr),\
                            std::forward<Args>(args)...)

    switch (expr->kind) {
        case ExpressionKind::Invalid: return visitor.visitInvalid(*expr, std::forward<Args>(args)...);
        CASE(IntegerLiteral, IntegerLiteral);
        CASE(RealLiteral, RealLiteral);
        CASE(UnbasedUnsizedIntegerLiteral, UnbasedUnsizedIntegerLiteral);
        CASE(NullLiteral, NullLiteral);
        CASE(StringLiteral, StringLiteral);
        CASE(NamedValue, NamedValueExpression);
        CASE(UnaryOp, UnaryExpression);
        CASE(BinaryOp, BinaryExpression);
        CASE(ConditionalOp, ConditionalExpression);
        CASE(Assignment, AssignmentExpression);
        CASE(Concatenation, ConcatenationExpression);
        CASE(Replication, ReplicationExpression);
        CASE(ElementSelect, ElementSelectExpression);
        CASE(RangeSelect, RangeSelectExpression);
        CASE(MemberAccess, MemberAccessExpression);
        CASE(Call, CallExpression);
        CASE(Conversion, ConversionExpression);
        CASE(DataType, DataTypeExpression);
    }
#undef CASE
    // clang-format on
    THROW_UNREACHABLE;
}

} // namespace detail

template<typename TVisitor, typename... Args>
decltype(auto) Expression::visit(TVisitor& visitor, Args&&... args) const {
    return detail::visitExpression(this, visitor, std::forward<Args>(args)...);
}

template<typename TVisitor, typename... Args>
decltype(auto) Expression::visit(TVisitor& visitor, Args&&... args) {
    return detail::visitExpression(this, visitor, std::forward<Args>(args)...);
}

} // namespace slang