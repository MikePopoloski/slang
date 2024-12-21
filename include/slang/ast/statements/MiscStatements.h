//------------------------------------------------------------------------------
//! @file MiscStatements.h
//! @brief Miscellaneous statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Statement.h"

namespace slang::ast {

class VariableSymbol;
class RandSeqProductionSymbol;

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class SLANG_EXPORT EmptyStatement : public Statement {
public:
    explicit EmptyStatement(SourceRange sourceRange) :
        Statement(StatementKind::Empty, sourceRange) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Empty; }
};

/// Represents a disable statement.
class SLANG_EXPORT DisableStatement : public Statement {
public:
    /// The target of the disable.
    const Expression& target;

    DisableStatement(const Expression& target, SourceRange sourceRange) :
        Statement(StatementKind::Disable, sourceRange), target(target) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::DisableStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Disable; }
};

/// Represents a variable declaration in a statement context.
class SLANG_EXPORT VariableDeclStatement : public Statement {
public:
    /// The variable that was declared.
    const VariableSymbol& symbol;

    VariableDeclStatement(const VariableSymbol& symbol, SourceRange sourceRange) :
        Statement(StatementKind::VariableDeclaration, sourceRange), symbol(symbol) {}

    EvalResult evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::VariableDeclaration; }
};

/// Represents an expression that is executed as a standalone statement.
class SLANG_EXPORT ExpressionStatement : public Statement {
public:
    /// The expression to execute.
    const Expression& expr;

    ExpressionStatement(const Expression& expr, SourceRange sourceRange) :
        Statement(StatementKind::ExpressionStatement, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ExpressionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::VoidCastedCallStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents a statement that has an associated timing control.
class SLANG_EXPORT TimedStatement : public Statement {
public:
    /// The timing that controls the statement.
    const TimingControl& timing;

    /// The statement.
    const Statement& stmt;

    TimedStatement(const TimingControl& timing, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Timed, sourceRange), timing(timing), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::TimingControlStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Timed; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return timing.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return stmt.visit(visitor);
    }
};

/// Represents an immediate assertion statement.
class SLANG_EXPORT ImmediateAssertionStatement : public Statement {
public:
    /// The assertion condition.
    const Expression& cond;

    /// An optional action to take if the assertion passes.
    const Statement* ifTrue;

    /// An optional action to take if the assertion fails.
    const Statement* ifFalse;

    /// The kind of assertion.
    AssertionKind assertionKind;

    /// True if the assertion is a "deferred" immediate assertion.
    bool isDeferred;

    /// True if the assertion is declared "final".
    bool isFinal;

    ImmediateAssertionStatement(AssertionKind assertionKind, const Expression& cond,
                                const Statement* ifTrue, const Statement* ifFalse, bool isDeferred,
                                bool isFinal, SourceRange sourceRange) :
        Statement(StatementKind::ImmediateAssertion, sourceRange), cond(cond), ifTrue(ifTrue),
        ifFalse(ifFalse), assertionKind(assertionKind), isDeferred(isDeferred), isFinal(isFinal) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ImmediateAssertionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ImmediateAssertion; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

/// Represents a concurrent assertion statement.
class SLANG_EXPORT ConcurrentAssertionStatement : public Statement {
public:
    /// The assertion body.
    const AssertionExpr& propertySpec;

    /// An optional action to take if the assertion passes.
    const Statement* ifTrue;

    /// An optional action to take if the assertion fails.
    const Statement* ifFalse;

    /// The kind of assertion.
    AssertionKind assertionKind;

    ConcurrentAssertionStatement(AssertionKind assertionKind, const AssertionExpr& propertySpec,
                                 const Statement* ifTrue, const Statement* ifFalse,
                                 SourceRange sourceRange) :
        Statement(StatementKind::ConcurrentAssertion, sourceRange), propertySpec(propertySpec),
        ifTrue(ifTrue), ifFalse(ifFalse), assertionKind(assertionKind) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ConcurrentAssertionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ConcurrentAssertion; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return propertySpec.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

/// Represents a `disable fork` statement.
class SLANG_EXPORT DisableForkStatement : public Statement {
public:
    explicit DisableForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::DisableFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::DisableForkStatementSyntax& syntax);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::DisableFork; }
};

/// Represents a `wait` statement.
class SLANG_EXPORT WaitStatement : public Statement {
public:
    /// The wait condition.
    const Expression& cond;

    /// The statement to execute after the condition passes.
    const Statement& stmt;

    WaitStatement(const Expression& cond, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Wait, sourceRange), cond(cond), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Wait; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return stmt.visit(visitor);
    }
};

/// Represents a `wait fork` statement.
class SLANG_EXPORT WaitForkStatement : public Statement {
public:
    explicit WaitForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::WaitFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitForkStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::WaitFork; }
};

/// Represents a `wait_order` statement.
class SLANG_EXPORT WaitOrderStatement : public Statement {
public:
    /// A list of expressions denoting the events on which to wait, in order.
    std::span<const Expression* const> events;

    /// An optional statement to execute if the events all trigger in order.
    const Statement* ifTrue;

    /// An optional statement to execute if any of the events did not trigger in order.
    const Statement* ifFalse;

    WaitOrderStatement(std::span<const Expression* const> events, const Statement* ifTrue,
                       const Statement* ifFalse, SourceRange sourceRange) :
        Statement(StatementKind::WaitOrder, sourceRange), events(events), ifTrue(ifTrue),
        ifFalse(ifFalse) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitOrderStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::WaitOrder; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto ev : events)
            ev->visit(visitor);
    }
};

/// Represents an event triggering statement.
class SLANG_EXPORT EventTriggerStatement : public Statement {
public:
    /// An expression denoting the target event to trigger.
    const Expression& target;

    /// An optional timing control delaying the triggering.
    const TimingControl* timing;

    /// True if the event trigger is a non-blocking operation, and false otherwise.
    bool isNonBlocking;

    EventTriggerStatement(const Expression& target, const TimingControl* timing, bool isNonBlocking,
                          SourceRange sourceRange) :
        Statement(StatementKind::EventTrigger, sourceRange), target(target), timing(timing),
        isNonBlocking(isNonBlocking) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::EventTriggerStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::EventTrigger; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        target.visit(visitor);
        if (timing)
            timing->visit(visitor);
    }
};

/// Represents a procedural `assign` statement.
class SLANG_EXPORT ProceduralAssignStatement : public Statement {
public:
    /// The assignment expression.
    const Expression& assignment;

    /// True if this is a `force` statement and false if it's an `assign` statement.
    bool isForce;

    ProceduralAssignStatement(const Expression& assignment, bool isForce, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralAssign, sourceRange), assignment(assignment),
        isForce(isForce) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ProceduralAssignStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralAssign; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return assignment.visit(visitor);
    }
};

/// Represents a procedural `deassign` statement.
class SLANG_EXPORT ProceduralDeassignStatement : public Statement {
public:
    /// The target lvalue to deassign.
    const Expression& lvalue;

    /// True if this is a `release` statement and false if it's a `deassign` statement.
    bool isRelease;

    ProceduralDeassignStatement(const Expression& lvalue, bool isRelease, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralDeassign, sourceRange), lvalue(lvalue),
        isRelease(isRelease) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ProceduralDeassignStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralDeassign; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return lvalue.visit(visitor);
    }
};

/// Represents a `randcase` statement.
class SLANG_EXPORT RandCaseStatement : public Statement {
public:
    /// An item in the randcase list.
    struct Item {
        /// The expression to match against.
        not_null<const Expression*> expr;

        /// The statement to execute upon a match.
        not_null<const Statement*> stmt;
    };

    /// The list of items to pick from.
    std::span<Item const> items;

    RandCaseStatement(std::span<Item const> items, SourceRange sourceRange) :
        Statement(StatementKind::RandCase, sourceRange), items(items) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::RandCaseStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandCase; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& item : items)
            item.expr->visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        for (auto& item : items)
            item.stmt->visit(visitor);
    }
};

/// Represents a `randsequence` statement.
class SLANG_EXPORT RandSequenceStatement : public Statement {
public:
    /// A pointer to the first production that starts the random sequence,
    /// or nullptr if the sequence is empty.
    const RandSeqProductionSymbol* firstProduction;

    RandSequenceStatement(const RandSeqProductionSymbol* firstProduction, SourceRange sourceRange) :
        Statement(StatementKind::RandSequence, sourceRange), firstProduction(firstProduction) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::RandSequenceStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandSequence; }
};

/// Represents a procedural checker instantiation statement.
class SLANG_EXPORT ProceduralCheckerStatement : public Statement {
public:
    /// A list of checkers to instantiate.
    std::span<const Symbol* const> instances;

    ProceduralCheckerStatement(std::span<const Symbol* const> instances, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralChecker, sourceRange), instances(instances) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::CheckerInstanceStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralChecker; }
};

} // namespace slang::ast
