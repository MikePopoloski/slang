//------------------------------------------------------------------------------
//! @file ASTVisitor.h
//! @brief AST traversal
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Constraints.h"
#include "slang/ast/Patterns.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/statements/ConditionalStatements.h"
#include "slang/ast/statements/LoopStatements.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SpecifySymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/util/TypeTraits.h"

namespace slang::ast {

template<typename T, typename TVisitor>
concept HasVisitExprs = requires(const T& t, TVisitor&& visitor) { t.visitExprs(visitor); };

/// @brief A base class for AST visitors
///
/// This class provides default visitors that can visit each child
/// of an AST node recursively. Statement and expression trees under
/// each node will only be visited if the corresponding template argument
/// is set to true.
///
/// You provide custom logic for specific node types by including a
/// handle(const Type& t) method in your derived class. If you provide
/// such a handler, by default child nodes of that node will not be
/// visited -- you can include that behavior by invoking @a visitDefault
/// in your handler.
///
template<typename TDerived, bool VisitStatements, bool VisitExpressions, bool VisitBad = false>
class ASTVisitor {
#define DERIVED *static_cast<TDerived*>(this)
public:
    /// The visit() entry point for visiting AST nodes.
    template<typename T>
    void visit(const T& t) {
        if constexpr (!VisitBad && requires { t.bad(); }) {
            if (t.bad())
                return;
        }

        if constexpr (requires { (DERIVED).handle(t); })
            (DERIVED).handle(t);
        else if constexpr (requires { (DERIVED)(DERIVED, t); })
            (DERIVED)(DERIVED, t);
        else
            visitDefault(t);
    }

    /// The default visit implementation, which is to descend into child nodes.
    /// You can invoke this from custom node handlers to get the default behavior.
    template<typename T>
    void visitDefault(const T& t) {
        if constexpr (VisitExpressions && HasVisitExprs<T, TDerived>) {
            t.visitExprs(DERIVED);
        }

        if constexpr (VisitStatements && requires { t.visitStmts(DERIVED); }) {
            t.visitStmts(DERIVED);
        }

        if constexpr (VisitExpressions && std::is_base_of_v<Symbol, T>) {
            if (auto declaredType = t.getDeclaredType()) {
                if (auto init = declaredType->getInitializer())
                    init->visit(DERIVED);
            }
        }

        if constexpr (std::is_base_of_v<GenericClassDefSymbol, T>) {
            for (auto&& spec : t.specializations())
                spec.visit(DERIVED);
        }

        if constexpr (std::is_base_of_v<Scope, T>) {
            for (auto& member : t.members())
                member.visit(DERIVED);
        }

        if constexpr (std::is_same_v<InstanceSymbol, T> ||
                      std::is_same_v<CheckerInstanceSymbol, T>) {
            t.body.visit(DERIVED);
        }
    }

#undef DERIVED
};

/// @brief Creates an ASTVisitor out of the provided handler functions.
///
/// The provided callable arguments must take two parameters, the first of which
/// is the visitor object itself (so that you can call visitDefault on it if
/// desired) and the second is the AST type to match against.
///
/// For example, to create a visitor that will count all of the BinaryExpressions
/// in an AST:
///
/// @code
/// int count = 0;
/// makeVisitor([&](auto& visitor, const BinaryExpression& expr) {
///     count++;
///     visitor.visitDefault(expr);
/// })
/// @endcode
///
template<typename... Functions>
auto makeVisitor(Functions... funcs) {
    struct Result : public Functions..., public ASTVisitor<Result, true, true> {
        Result(Functions... funcs) : Functions(std::move(funcs))... {}
        using Functions::operator()...;
    };
    return Result(std::move(funcs)...);
}

/// @cond NOPE

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
        SYMBOL(Definition);
        SYMBOL(Attribute);
        SYMBOL(TransparentMember);
        SYMBOL(EmptyMember);
        SYMBOL(EnumValue);
        SYMBOL(ForwardingTypedef);
        SYMBOL(Parameter);
        SYMBOL(TypeParameter);
        SYMBOL(Port);
        SYMBOL(MultiPort);
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
        SYMBOL(ModportClocking);
        SYMBOL(ContinuousAssign);
        SYMBOL(Genvar);
        SYMBOL(ElabSystemTask);
        SYMBOL(GenericClassDef);
        SYMBOL(MethodPrototype);
        SYMBOL(UninstantiatedDef);
        SYMBOL(Iterator);
        SYMBOL(PatternVar);
        SYMBOL(ConstraintBlock);
        SYMBOL(DefParam);
        SYMBOL(Specparam);
        SYMBOL(Primitive);
        SYMBOL(PrimitivePort);
        SYMBOL(PrimitiveInstance);
        SYMBOL(SpecifyBlock);
        SYMBOL(Sequence);
        SYMBOL(Property);
        SYMBOL(AssertionPort);
        SYMBOL(ClockingBlock);
        SYMBOL(ClockVar);
        SYMBOL(LocalAssertionVar);
        SYMBOL(LetDecl);
        SYMBOL(Checker);
        SYMBOL(CheckerInstance);
        SYMBOL(CheckerInstanceBody);
        SYMBOL(RandSeqProduction);
        SYMBOL(CovergroupBody);
        SYMBOL(Coverpoint);
        SYMBOL(CoverCross);
        SYMBOL(CoverCrossBody);
        SYMBOL(CoverageBin);
        SYMBOL(TimingPath);
        SYMBOL(PulseStyle);
        SYMBOL(SystemTimingCheck);
        SYMBOL(AnonymousProgram);
        SYMBOL(NetAlias);
        SYMBOL(ConfigBlock);
        TYPE(PredefinedIntegerType);
        TYPE(ScalarType);
        TYPE(FloatingType);
        TYPE(EnumType);
        TYPE(PackedArrayType);
        TYPE(FixedSizeUnpackedArrayType);
        TYPE(DynamicArrayType);
        TYPE(DPIOpenArrayType);
        TYPE(AssociativeArrayType);
        TYPE(QueueType);
        TYPE(PackedStructType);
        TYPE(UnpackedStructType);
        TYPE(PackedUnionType);
        TYPE(UnpackedUnionType);
        TYPE(ClassType);
        TYPE(CovergroupType);
        TYPE(VoidType);
        TYPE(NullType);
        TYPE(CHandleType);
        TYPE(StringType);
        TYPE(EventType);
        TYPE(UnboundedType);
        TYPE(TypeRefType);
        TYPE(UntypedType);
        TYPE(SequenceType);
        TYPE(PropertyType);
        TYPE(VirtualInterfaceType);
        TYPE(ErrorType);
        TYPE(NetType);
    }
#undef TYPE
#undef SYMBOL
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Statement::visit(TVisitor&& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case StatementKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidStatement);
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
        CASE(PatternCase, PatternCaseStatement);
        CASE(ForLoop, ForLoopStatement);
        CASE(RepeatLoop, RepeatLoopStatement);
        CASE(ForeachLoop, ForeachLoopStatement);
        CASE(WhileLoop, WhileLoopStatement);
        CASE(DoWhileLoop, DoWhileLoopStatement);
        CASE(ForeverLoop, ForeverLoopStatement);
        CASE(Timed, TimedStatement);
        CASE(ImmediateAssertion, ImmediateAssertionStatement);
        CASE(ConcurrentAssertion, ConcurrentAssertionStatement);
        CASE(DisableFork, DisableForkStatement);
        CASE(Wait, WaitStatement);
        CASE(WaitFork, WaitForkStatement);
        CASE(WaitOrder, WaitOrderStatement);
        CASE(EventTrigger, EventTriggerStatement);
        CASE(ProceduralAssign, ProceduralAssignStatement);
        CASE(ProceduralDeassign, ProceduralDeassignStatement);
        CASE(RandCase, RandCaseStatement);
        CASE(RandSequence, RandSequenceStatement);
        CASE(ProceduralChecker, ProceduralCheckerStatement);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) TimingControl::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case TimingControlKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidTimingControl);
        CASE(Delay, DelayControl);
        CASE(Delay3, Delay3Control);
        CASE(SignalEvent, SignalEventControl);
        CASE(EventList, EventListControl);
        CASE(ImplicitEvent, ImplicitEventControl);
        CASE(RepeatedEvent, RepeatedEventControl);
        CASE(OneStepDelay, OneStepDelayControl);
        CASE(CycleDelay, CycleDelayControl);
        CASE(BlockEventList, BlockEventListControl);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TExpression, typename TVisitor, typename... Args>
decltype(auto) Expression::visitExpression(TExpression* expr, TVisitor&& visitor,
                                           Args&&... args) const {
    // clang-format off
#define CASE(k, n) case ExpressionKind::k: return visitor.visit(\
                        *static_cast<std::conditional_t<std::is_const_v<TExpression>, const n*, n*>>(expr),\
                            std::forward<Args>(args)...)

    switch (expr->kind) {
        CASE(Invalid, InvalidExpression);
        CASE(IntegerLiteral, IntegerLiteral);
        CASE(RealLiteral, RealLiteral);
        CASE(TimeLiteral, TimeLiteral);
        CASE(UnbasedUnsizedIntegerLiteral, UnbasedUnsizedIntegerLiteral);
        CASE(NullLiteral, NullLiteral);
        CASE(UnboundedLiteral, UnboundedLiteral);
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
        CASE(TypeReference, TypeReferenceExpression);
        CASE(ArbitrarySymbol, ArbitrarySymbolExpression);
        CASE(LValueReference, LValueReferenceExpression);
        CASE(SimpleAssignmentPattern, SimpleAssignmentPatternExpression);
        CASE(StructuredAssignmentPattern, StructuredAssignmentPatternExpression);
        CASE(ReplicatedAssignmentPattern, ReplicatedAssignmentPatternExpression);
        CASE(EmptyArgument, EmptyArgumentExpression);
        CASE(ValueRange, ValueRangeExpression);
        CASE(Dist, DistExpression);
        CASE(NewArray, NewArrayExpression);
        CASE(NewClass, NewClassExpression);
        CASE(NewCovergroup, NewCovergroupExpression);
        CASE(CopyClass, CopyClassExpression);
        CASE(MinTypMax, MinTypMaxExpression);
        CASE(ClockingEvent, ClockingEventExpression);
        CASE(AssertionInstance, AssertionInstanceExpression);
        CASE(TaggedUnion, TaggedUnionExpression);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
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
    for (auto conn : getPortConnections()) {
        if (auto expr = conn->getExpression())
            expr->visit(visitor);
    }
}

template<typename TVisitor>
void PrimitiveInstanceSymbol::visitExprs(TVisitor&& visitor) const {
    for (auto conn : getPortConnections())
        conn->visit(visitor);
}

template<typename TVisitor>
void CheckerInstanceSymbol::visitExprs(TVisitor&& visitor) const {
    for (auto& conn : getPortConnections()) {
        std::visit(
            [&](auto&& arg) {
                if (arg)
                    arg->visit(visitor);
            },
            conn.actual);
        if (auto expr = conn.getOutputInitialExpr())
            expr->visit(visitor);
    }
}

template<typename TVisitor>
decltype(auto) SubroutineSymbol::visitStmts(TVisitor&& visitor) const {
    return getBody().visit(visitor);
}

template<typename TVisitor, typename... Args>
decltype(auto) Constraint::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case ConstraintKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidConstraint);
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
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) AssertionExpr::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case AssertionExprKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidAssertionExpr);
        CASE(Simple, SimpleAssertionExpr);
        CASE(SequenceConcat, SequenceConcatExpr);
        CASE(SequenceWithMatch, SequenceWithMatchExpr);
        CASE(Unary, UnaryAssertionExpr);
        CASE(Binary, BinaryAssertionExpr);
        CASE(FirstMatch, FirstMatchAssertionExpr);
        CASE(Clocking, ClockingAssertionExpr);
        CASE(StrongWeak, StrongWeakAssertionExpr);
        CASE(Abort, AbortAssertionExpr);
        CASE(Conditional, ConditionalAssertionExpr);
        CASE(Case, CaseAssertionExpr);
        CASE(DisableIff, DisableIffAssertionExpr);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) BinsSelectExpr::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case BinsSelectExprKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidBinsSelectExpr);
        CASE(Condition, ConditionBinsSelectExpr);
        CASE(Unary, UnaryBinsSelectExpr);
        CASE(Binary, BinaryBinsSelectExpr);
        CASE(SetExpr, SetExprBinsSelectExpr);
        CASE(WithFilter, BinSelectWithFilterExpr);
        CASE(CrossId, CrossIdBinsSelectExpr);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) Pattern::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case PatternKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Invalid, InvalidPattern);
        CASE(Wildcard, WildcardPattern);
        CASE(Constant, ConstantPattern);
        CASE(Variable, VariablePattern);
        CASE(Tagged, TaggedPattern);
        CASE(Structure, StructurePattern);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

template<typename TVisitor, typename... Args>
decltype(auto) RandSeqProductionSymbol::ProdBase::visit(TVisitor& visitor, Args&&... args) const {
    // clang-format off
#define CASE(k, n) case RandSeqProductionSymbol::ProdKind::k: return visitor.visit(*static_cast<const n*>(this), std::forward<Args>(args)...)
    switch (kind) {
        CASE(Item, ProdItem);
        CASE(CodeBlock, CodeBlockProd);
        CASE(IfElse, IfElseProd);
        CASE(Repeat, RepeatProd);
        CASE(Case, CaseProd);
    }
#undef CASE
    // clang-format on
    SLANG_UNREACHABLE;
}

/// @endcond

} // namespace slang::ast
