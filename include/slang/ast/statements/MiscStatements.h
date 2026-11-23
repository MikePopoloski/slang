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
class StatementBlockSymbol;

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class SLANG_EXPORT EmptyStatement final : public Statement {
public:
    explicit EmptyStatement(SourceRange sourceRange) :
        Statement(StatementKind::Empty, sourceRange) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Empty; }
};

/// Represents a disable statement.
class SLANG_EXPORT DisableStatement final : public Statement {
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
class SLANG_EXPORT VariableDeclStatement final : public Statement {
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
class SLANG_EXPORT ExpressionStatement final : public Statement {
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
class SLANG_EXPORT TimedStatement final : public Statement {
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
class SLANG_EXPORT ImmediateAssertionStatement final : public Statement {
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
class SLANG_EXPORT ConcurrentAssertionStatement final : public Statement {
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
class SLANG_EXPORT DisableForkStatement final : public Statement {
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
class SLANG_EXPORT WaitStatement final : public Statement {
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
class SLANG_EXPORT WaitForkStatement final : public Statement {
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
class SLANG_EXPORT WaitOrderStatement final : public Statement {
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
class SLANG_EXPORT EventTriggerStatement final : public Statement {
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
class SLANG_EXPORT ProceduralAssignStatement final : public Statement {
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
class SLANG_EXPORT ProceduralDeassignStatement final : public Statement {
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
class SLANG_EXPORT RandCaseStatement final : public Statement {
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
class SLANG_EXPORT RandSequenceStatement final : public Statement {
public:
    /// Specifies the kinds of productions that can appear in a rule.
    enum class ProdKind {
        /// A reference to another production, with optional arguments.
        Item,

        /// A block of procedural code.
        CodeBlock,

        /// A production chosen by an if-else condition.
        IfElse,

        /// A production repeated a given number of times.
        Repeat,

        /// A production chosen by a case statement.
        Case
    };

    /// The base class for productions in a rule.
    struct ProdBase {
        /// The kind of production.
        ProdKind kind;

        explicit ProdBase(ProdKind kind) : kind(kind) {}

        /// Casts this production to the given concrete derived type.
        /// Asserts that the kind matches.
        template<typename T>
        T& as() {
            SLANG_ASSERT(T::isKind(kind));
            return *static_cast<T*>(this);
        }

        /// Casts this production to the given concrete derived type.
        /// Asserts that the kind matches.
        template<typename T>
        const T& as() const {
            SLANG_ASSERT(T::isKind(kind));
            return *static_cast<const T*>(this);
        }

        /// Tries to cast this production to the given concrete derived type.
        /// Returns nullptr if the kind doesn't match.
        template<typename T>
        T* as_if() {
            if (!T::isKind(kind))
                return nullptr;
            return static_cast<T*>(this);
        }

        /// Tries to cast this production to the given concrete derived type.
        /// Returns nullptr if the kind doesn't match.
        template<typename T>
        const T* as_if() const {
            if (!T::isKind(kind))
                return nullptr;
            return static_cast<const T*>(this);
        }

        /// Visits this production's concrete derived type via the provided visitor.
        template<typename TVisitor, typename... Args>
        decltype(auto) visit(TVisitor& visitor, Args&&... args) const;
    };

    /// A production item, which invokes another production.
    struct ProdItem : public ProdBase {
        /// The production being invoked, or nullptr if the name
        /// didn't refer to a valid production.
        const RandSeqProductionSymbol* target;

        /// The arguments passed to the production.
        std::span<const Expression* const> args;

        ProdItem(const RandSeqProductionSymbol* target, std::span<const Expression* const> args) :
            ProdBase(ProdKind::Item), target(target), args(args) {}

        static bool isKind(ProdKind kind) { return kind == ProdKind::Item; }

        /// Visits the argument expressions.
        template<typename TVisitor>
        void visitExprs(TVisitor&& visitor) const {
            for (auto arg : args)
                arg->visit(visitor);
        }
    };

    /// A block of procedural code that runs as part of a rule.
    struct CodeBlockProd : public ProdBase {
        /// The statement block that holds the code.
        not_null<const StatementBlockSymbol*> block;

        explicit CodeBlockProd(const StatementBlockSymbol& block) :
            ProdBase(ProdKind::CodeBlock), block(&block) {}

        static bool isKind(ProdKind kind) { return kind == ProdKind::CodeBlock; }
    };

    /// A production that chooses between items based on a condition.
    struct IfElseProd : public ProdBase {
        /// The condition expression.
        not_null<const Expression*> expr;

        /// The item to produce if the condition is true.
        ProdItem ifItem;

        /// The item to produce if the condition is false, if there is one.
        std::optional<ProdItem> elseItem;

        IfElseProd(const Expression& expr, ProdItem ifItem, std::optional<ProdItem> elseItem) :
            ProdBase(ProdKind::IfElse), expr(&expr), ifItem(ifItem), elseItem(elseItem) {}

        static bool isKind(ProdKind kind) { return kind == ProdKind::IfElse; }
    };

    /// A production that repeats an item a number of times.
    struct RepeatProd : public ProdBase {
        /// The expression giving the number of repetitions.
        not_null<const Expression*> expr;

        /// The item to repeat.
        ProdItem item;

        RepeatProd(const Expression& expr, ProdItem item) :
            ProdBase(ProdKind::Repeat), expr(&expr), item(item) {}

        static bool isKind(ProdKind kind) { return kind == ProdKind::Repeat; }
    };

    /// An item in a case production.
    struct CaseItem {
        /// The expressions to match against the case condition.
        std::span<const Expression* const> expressions;

        /// The item to produce if one of the expressions matches.
        ProdItem item;
    };

    /// A production that chooses an item with a case statement.
    struct CaseProd : public ProdBase {
        /// The case condition expression.
        not_null<const Expression*> expr;

        /// The case items.
        std::span<const CaseItem> items;

        /// The item to produce if no case item matches, if there is one.
        std::optional<ProdItem> defaultItem;

        CaseProd(const Expression& expr, std::span<const CaseItem> items,
                 std::optional<ProdItem> defaultItem) :
            ProdBase(ProdKind::Case), expr(&expr), items(items), defaultItem(defaultItem) {}

        static bool isKind(ProdKind kind) { return kind == ProdKind::Case; }
    };

    /// A rule of a production, which is one of its alternatives.
    struct Rule {
        /// The statement block that scopes the rule, holding the variables
        /// that refer to the values produced by its items.
        not_null<const StatementBlockSymbol*> ruleBlock;

        /// The productions that make up the rule, in order.
        std::span<const ProdBase* const> prods;

        /// The weight of the rule, if one was given.
        const Expression* weightExpr;

        /// The bias of a rand join, if one was given.
        const Expression* randJoinExpr;

        /// The code block that follows the weight, if there is one.
        std::optional<CodeBlockProd> codeBlock;

        /// Whether the rule is a rand join.
        bool isRandJoin;

        Rule(const StatementBlockSymbol& ruleBlock, std::span<const ProdBase* const> prods,
             const Expression* weightExpr, const Expression* randJoinExpr,
             std::optional<CodeBlockProd> codeBlock, bool isRandJoin) :
            ruleBlock(&ruleBlock), prods(prods), weightExpr(weightExpr), randJoinExpr(randJoinExpr),
            codeBlock(codeBlock), isRandJoin(isRandJoin) {}
    };

    /// A production in the random sequence along with its rules. The rules
    /// belong to the statement rather than the production symbol because they
    /// are bound in the context of the enclosing procedure [18.17.7].
    struct Production {
        /// The symbol that declares the production.
        not_null<const RandSeqProductionSymbol*> symbol;

        /// The rules of the production.
        std::span<const Rule> rules;
    };

    /// A pointer to the first production that starts the random sequence,
    /// or nullptr if the sequence is empty.
    const RandSeqProductionSymbol* firstProduction;

    /// A list of all productions in the random sequence.
    std::span<const Production> productions;

    RandSequenceStatement(const RandSeqProductionSymbol* firstProduction,
                          std::span<const Production> productions, SourceRange sourceRange) :
        Statement(StatementKind::RandSequence, sourceRange), firstProduction(firstProduction),
        productions(productions) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::RandSequenceStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandSequence; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& production : productions) {
            for (auto& rule : production.rules) {
                for (auto prod : rule.prods) {
                    switch (prod->kind) {
                        case ProdKind::Item:
                            prod->as<ProdItem>().visitExprs(visitor);
                            break;
                        case ProdKind::CodeBlock:
                            break;
                        case ProdKind::IfElse: {
                            auto& iep = prod->as<IfElseProd>();
                            iep.expr->visit(visitor);
                            iep.ifItem.visitExprs(visitor);
                            if (iep.elseItem)
                                iep.elseItem->visitExprs(visitor);
                            break;
                        }
                        case ProdKind::Repeat: {
                            auto& rp = prod->as<RepeatProd>();
                            rp.expr->visit(visitor);
                            rp.item.visitExprs(visitor);
                            break;
                        }
                        case ProdKind::Case: {
                            auto& cp = prod->as<CaseProd>();
                            cp.expr->visit(visitor);
                            if (cp.defaultItem)
                                cp.defaultItem->visitExprs(visitor);

                            for (auto& item : cp.items) {
                                for (auto expr : item.expressions)
                                    expr->visit(visitor);

                                item.item.visitExprs(visitor);
                            }
                            break;
                        }
                    }
                }

                if (rule.weightExpr)
                    rule.weightExpr->visit(visitor);

                if (rule.randJoinExpr)
                    rule.randJoinExpr->visit(visitor);
            }
        }
    }

private:
    // Creates the rules of a production. Code blocks in the rules are nested in
    // the procedure that encloses the randsequence [18.17.7], so they are bound
    // only here, with the context of the statement.
    static std::span<const Rule> createRules(const RandSeqProductionSymbol& production,
                                             const ASTContext& parentContext);
    static Rule createRule(const syntax::RsRuleSyntax& syntax, const ASTContext& context,
                           const StatementBlockSymbol& ruleBlock);
    static ProdItem createProdItem(const syntax::RsProdItemSyntax& syntax,
                                   const ASTContext& context);
    static const CaseProd& createCaseProd(const syntax::RsCaseSyntax& syntax,
                                          const ASTContext& context);
};

/// Represents a procedural checker instantiation statement.
class SLANG_EXPORT ProceduralCheckerStatement final : public Statement {
public:
    /// A list of checkers to instantiate.
    std::span<const Symbol* const> instances;

    ProceduralCheckerStatement(std::span<const Symbol* const> instances, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralChecker, sourceRange), instances(instances) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::CheckerInstanceStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralChecker; }
};

} // namespace slang::ast
