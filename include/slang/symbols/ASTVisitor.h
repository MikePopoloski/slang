//------------------------------------------------------------------------------
//! @file ASTVisitor.h
//! @brief AST traversal
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/Constraints.h"
#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/binding/PatternExpressions.h"
#include "slang/binding/SelectExpressions.h"
#include "slang/binding/Statements.h"
#include "slang/binding/TimingControl.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/types/AllTypes.h"
#include "slang/types/NetType.h"
#include "slang/util/TypeTraits.h"

namespace slang {

/// Use this type as a base class for AST visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived, bool VisitStatements, bool VisitExpressions>
struct ASTVisitor {
    template<typename T, typename Arg>
    using handle_t = decltype(std::declval<T>().handle(std::declval<Arg>()));

    template<typename T, typename Arg>
    using op_t = decltype(std::declval<T>()(std::declval<Arg>()));

    template<typename T>
    using getBody_t = decltype(std::declval<T>().getBody());

    template<typename T, typename Arg>
    using visitExprs_t = decltype(std::declval<T>().visitExprs(std::declval<Arg>()));

    template<typename T, typename Arg>
    using visitStmts_t = decltype(std::declval<T>().visitStmts(std::declval<Arg>()));

#define DERIVED *static_cast<TDerived*>(this)

public:
    template<typename T>
    void visit(const T& t) {
        if constexpr (is_detected_v<handle_t, TDerived, T>)
            static_cast<TDerived*>(this)->handle(t);
        else if constexpr (is_detected_v<op_t, TDerived, T>)
            (DERIVED)(t);
        else
            visitDefault(t);
    }

    template<typename T>
    void visitDefault(const T& t) {
        if constexpr (VisitExpressions && is_detected_v<visitExprs_t, T, TDerived>) {
            t.visitExprs(DERIVED);
        }

        if constexpr (VisitStatements && is_detected_v<visitStmts_t, T, TDerived>) {
            t.visitStmts(DERIVED);
        }

        if constexpr (VisitExpressions && std::is_base_of_v<Symbol, T>) {
            if (auto declaredType = t.getDeclaredType()) {
                if (auto init = declaredType->getInitializer())
                    init->visit(DERIVED);
            }
        }

        if constexpr (std::is_base_of_v<Scope, T>) {
            for (auto& member : t.members())
                member.visit(DERIVED);
        }

        if constexpr (std::is_same_v<InstanceSymbol, T>) {
            t.body.visit(DERIVED);
        }
    }

    void visitDefault(const Symbol&) {}
    void visitDefault(const Expression&) {}
    void visitDefault(const Statement&) {}

    void visitInvalid(const Expression&) {}
    void visitInvalid(const Statement&) {}
    void visitInvalid(const TimingControl&) {}
    void visitInvalid(const Constraint&) {}

#undef DERIVED
};

template<typename... Functions>
auto makeVisitor(Functions... funcs) {
    struct Result : public Functions..., public ASTVisitor<Result, true, true> {
        Result(Functions... funcs) : Functions(std::move(funcs))... {}
        using Functions::operator()...;
    };
    return Result(std::move(funcs)...);
}

template<typename TVisitor, typename... Args>
decltype(auto) Symbol::visit(TVisitor&& visitor, Args&&... args) const {
    // clang-format off
#define SYMBOL(k) case SymbolKind::k: return visitor.visit(*static_cast<const k##Symbol*>(this), std::forward<Args>(args)...)
#define TYPE(k) case SymbolKind::k: return visitor.visit(*static_cast<const k*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case SymbolKind::Unknown: return visitor.visit(*this, std::forward<Args>(args)...);
        case SymbolKind::DeferredMember: return visitor.visit(*this, std::forward<Args>(args)...);
        case SymbolKind::TypeAlias: return visitor.visit(*static_cast<const TypeAliasType*>(this), std::forward<Args>(args)...);
        SYMBOL(Root);
        SYMBOL(CompilationUnit);
        SYMBOL(Attribute);
        SYMBOL(TransparentMember);
        SYMBOL(EmptyMember);
        SYMBOL(EnumValue);
        SYMBOL(ForwardingTypedef);
        SYMBOL(Parameter);
        SYMBOL(TypeParameter);
        SYMBOL(Port);
        SYMBOL(InterfacePort);
        SYMBOL(Instance);
        SYMBOL(InstanceBody);
        SYMBOL(InstanceArray);
        SYMBOL(Package);
        SYMBOL(ExplicitImport);
        SYMBOL(WildcardImport);
        SYMBOL(GenerateBlock);
        SYMBOL(GenerateBlockArray);
        SYMBOL(ProceduralBlock);
        SYMBOL(StatementBlock);
        SYMBOL(Net);
        SYMBOL(Variable);
        SYMBOL(FormalArgument);
        SYMBOL(Field);
        SYMBOL(ClassProperty);
        SYMBOL(Subroutine);
        SYMBOL(Modport);
        SYMBOL(ModportPort);
        SYMBOL(ContinuousAssign);
        SYMBOL(Genvar);
        SYMBOL(Gate);
        SYMBOL(GateArray);
        SYMBOL(ElabSystemTask);
        SYMBOL(GenericClassDef);
        SYMBOL(MethodPrototype);
        SYMBOL(UnknownModule);
        SYMBOL(Iterator);
        SYMBOL(ConstraintBlock);
        TYPE(PredefinedIntegerType);
        TYPE(ScalarType);
        TYPE(FloatingType);
        TYPE(EnumType);
        TYPE(PackedArrayType);
        TYPE(FixedSizeUnpackedArrayType);
        TYPE(DynamicArrayType);
        TYPE(AssociativeArrayType);
        TYPE(QueueType);
        TYPE(PackedStructType);
        TYPE(UnpackedStructType);
        TYPE(PackedUnionType);
        TYPE(UnpackedUnionType);
        TYPE(ClassType);
        TYPE(VoidType);
        TYPE(NullType);
        TYPE(CHandleType);
        TYPE(StringType);
        TYPE(EventType);
        TYPE(ErrorType);
        TYPE(NetType);
    }
#undef TYPE
#undef SYMBOL
    // clang-format on
    THROW_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Statement::visit(TVisitor&& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case StatementKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case StatementKind::Invalid: return visitor.visitInvalid(*this, std::forward<Args>(args)...);
        CASE(Empty, EmptyStatement);
        CASE(List, StatementList);
        CASE(Block, BlockStatement);
        CASE(ExpressionStatement, ExpressionStatement);
        CASE(VariableDeclaration, VariableDeclStatement);
        CASE(Return, ReturnStatement);
        CASE(Break, BreakStatement);
        CASE(Continue, ContinueStatement);
        CASE(Disable, DisableStatement);
        CASE(Conditional, ConditionalStatement);
        CASE(Case, CaseStatement);
        CASE(ForLoop, ForLoopStatement);
        CASE(RepeatLoop, RepeatLoopStatement);
        CASE(ForeachLoop, ForeachLoopStatement);
        CASE(WhileLoop, WhileLoopStatement);
        CASE(DoWhileLoop, DoWhileLoopStatement);
        CASE(ForeverLoop, ForeverLoopStatement);
        CASE(Timed, TimedStatement);
        CASE(Assertion, AssertionStatement);
        CASE(DisableFork, DisableForkStatement);
        CASE(Wait, WaitStatement);
        CASE(WaitFork, WaitForkStatement);
        CASE(WaitOrder, WaitOrderStatement);
        CASE(EventTrigger, EventTriggerStatement);
        CASE(ProceduralAssign, ProceduralAssignStatement);
        CASE(ProceduralDeassign, ProceduralDeassignStatement);
    }
#undef CASE
    // clang-format on
    THROW_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) TimingControl::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case TimingControlKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case TimingControlKind::Invalid: return visitor.visit(*this, std::forward<Args>(args)...);
        CASE(Delay, DelayControl);
        CASE(Delay3, Delay3Control);
        CASE(SignalEvent, SignalEventControl);
        CASE(EventList, EventListControl);
        CASE(ImplicitEvent, ImplicitEventControl);
        CASE(RepeatedEvent, RepeatedEventControl);
    }
#undef CASE
    // clang-format on
    THROW_UNREACHABLE;
}

template<typename TExpression, typename TVisitor, typename... Args>
decltype(auto) Expression::visitExpression(TExpression* expr, TVisitor&& visitor,
                                           Args&&... args) const {
    // clang-format off
#define CASE(k, n) case ExpressionKind::k: return visitor.visit(\
                        *static_cast<std::conditional_t<std::is_const_v<TExpression>, const n*, n*>>(expr),\
                            std::forward<Args>(args)...)

    switch (expr->kind) {
        case ExpressionKind::Invalid: return visitor.visitInvalid(*expr, std::forward<Args>(args)...);
        CASE(IntegerLiteral, IntegerLiteral);
        CASE(RealLiteral, RealLiteral);
        CASE(TimeLiteral, TimeLiteral);
        CASE(UnbasedUnsizedIntegerLiteral, UnbasedUnsizedIntegerLiteral);
        CASE(NullLiteral, NullLiteral);
        CASE(StringLiteral, StringLiteral);
        CASE(NamedValue, NamedValueExpression);
        CASE(HierarchicalValue, HierarchicalValueExpression);
        CASE(UnaryOp, UnaryExpression);
        CASE(BinaryOp, BinaryExpression);
        CASE(ConditionalOp, ConditionalExpression);
        CASE(Inside, InsideExpression);
        CASE(Assignment, AssignmentExpression);
        CASE(Concatenation, ConcatenationExpression);
        CASE(Replication, ReplicationExpression);
        CASE(Streaming, StreamingConcatenationExpression);
        CASE(ElementSelect, ElementSelectExpression);
        CASE(RangeSelect, RangeSelectExpression);
        CASE(MemberAccess, MemberAccessExpression);
        CASE(Call, CallExpression);
        CASE(Conversion, ConversionExpression);
        CASE(DataType, DataTypeExpression);
        CASE(HierarchicalReference, HierarchicalReferenceExpression);
        CASE(LValueReference, LValueReferenceExpression);
        CASE(SimpleAssignmentPattern, SimpleAssignmentPatternExpression);
        CASE(StructuredAssignmentPattern, StructuredAssignmentPatternExpression);
        CASE(ReplicatedAssignmentPattern, ReplicatedAssignmentPatternExpression);
        CASE(EmptyArgument, EmptyArgumentExpression);
        CASE(OpenRange, OpenRangeExpression);
        CASE(Dist, DistExpression);
        CASE(NewArray, NewArrayExpression);
        CASE(NewClass, NewClassExpression);
        CASE(CopyClass, CopyClassExpression);
        CASE(MinTypMax, MinTypMaxExpression);
    }
#undef CASE
    // clang-format on
    THROW_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Expression::visit(TVisitor&& visitor, Args&&... args) const {
    return visitExpression(this, visitor, std::forward<Args>(args)...);
}

template<typename TVisitor, typename... Args>
decltype(auto) Expression::visit(TVisitor&& visitor, Args&&... args) {
    return visitExpression(this, visitor, std::forward<Args>(args)...);
}

template<typename TVisitor>
void InstanceSymbol::visitExprs(TVisitor&& visitor) const {
    resolvePortConnections();
    for (auto& [k, v] : *connections) {
        auto conn = reinterpret_cast<const PortConnection*>(v);
        if (conn && !conn->isInterfacePort && conn->expr)
            conn->expr->visit(visitor);
    }
}

template<typename TVisitor, typename... Args>
decltype(auto) Constraint::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case ConstraintKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        case ConstraintKind::Invalid: return visitor.visit(*this, std::forward<Args>(args)...);
        CASE(List, ConstraintList);
        CASE(Expression, ExpressionConstraint);
        CASE(Implication, ImplicationConstraint);
        CASE(Conditional, ConditionalConstraint);
        CASE(Uniqueness, UniquenessConstraint);
        CASE(DisableSoft, DisableSoftConstraint);
        CASE(SolveBefore, SolveBeforeConstraint);
        CASE(Foreach, ForeachConstraint);
    }
#undef CASE
    // clang-format on
    THROW_UNREACHABLE;
}

} // namespace slang
