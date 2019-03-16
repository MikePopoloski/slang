//------------------------------------------------------------------------------
// Statements.h
// Statement creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/EvalContext.h"

namespace slang {

class SequentialBlockSymbol;
class VariableSymbol;

// clang-format off
#define STATEMENT(x) \
    x(Invalid) \
    x(List) \
    x(SequentialBlock) \
    x(ExpressionStatement) \
    x(VariableDeclaration) \
    x(Return) \
    x(Conditional) \
    x(ForLoop)
ENUM(StatementKind, STATEMENT);
#undef STATEMENT

/// The base class for all statements in SystemVerilog.
class Statement {
public:
    /// The kind of statement; indicates the type of derived class.
    StatementKind kind;

    /// The syntax used to create this statement, if it was parsed from a source file.
    const StatementSyntax* syntax = nullptr;

    /// Indicates whether the statement is invalid.
    bool bad() const { return kind == StatementKind::Invalid; }

    /// Evaluates the statement under the given evaluation context. Returns true if
    /// evaluation should continue and false if something has gone wrong and the
    /// evaluation should be halted.
    bool eval(EvalContext& context) const;

    using BlockList = span<const SequentialBlockSymbol* const>;

    /// Binds a statement tree from the given syntax nodes.
    static const Statement& bind(const StatementSyntax& syntax, const BindContext& context,
                                 BlockList& blocks);

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit Statement(StatementKind kind) : kind(kind) {}

    static Statement& badStmt(Compilation& compilation, const Statement* stmt);
};

/// A wrapper around a statement syntax node and some associated symbols that can later
/// be turned into an actual statement tree. The point of this is to allow symbols to
/// defer statement binding until its actually needed.
class StatementBinder {
public:
    void setSyntax(const Scope& scope, const StatementSyntax& syntax);
    void setSyntax(const SequentialBlockSymbol& scope, const ForLoopStatementSyntax& syntax);
    void setItems(Scope& scope, const SyntaxList<SyntaxNode>& syntax);

    const Statement& getStatement(const Scope& scope, LookupLocation location) const;
    span<const SequentialBlockSymbol* const> getBlocks() const { return blocks; }

private:
    const Statement& bindStatement(const Scope& scope, LookupLocation location) const;

    std::variant<const StatementSyntax*, const SyntaxList<SyntaxNode>*> syntax;
    mutable const Statement* stmt = nullptr;
    span<const SequentialBlockSymbol* const> blocks;
};

/// Represents an invalid statement, which is usually generated and inserted
/// into a statement list due to violation of language semantics or type checking.
class InvalidStatement : public Statement {
public:
    /// A wrapped sub-statement that is considered invalid.
    const Statement* child;

    explicit InvalidStatement(const Statement* child) :
        Statement(StatementKind::Invalid), child(child) {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Invalid; }

    static const InvalidStatement Instance;
};

/// Represents a list of statements.
class StatementList : public Statement {
public:
    span<const Statement* const> list;

    explicit StatementList(span<const Statement* const> list) :
        Statement(StatementKind::List), list(list) {}

    bool eval(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::List; }
    static const StatementList Empty;
};

/// Represents a sequential block statement.
class SequentialBlockStatement : public Statement {
public:
    explicit SequentialBlockStatement(const SequentialBlockSymbol& block) :
        Statement(StatementKind::SequentialBlock), block(&block) {}

    explicit SequentialBlockStatement(const StatementList& list) :
        Statement(StatementKind::SequentialBlock), list(&list) {}

    const Statement& getStatements() const;
    bool eval(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax,
                                 const BindContext& context, BlockList& blocks);

    static bool isKind(StatementKind kind) { return kind == StatementKind::SequentialBlock; }

private:
    const SequentialBlockSymbol* block = nullptr;
    const StatementList* list = nullptr;
};

class ReturnStatement : public Statement {
public:
    const Expression* expr;

    explicit ReturnStatement(const Expression* expr) :
        Statement(StatementKind::Return), expr(expr) {}

    bool eval(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ReturnStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Return; }
};

class VariableDeclStatement : public Statement {
public:
    const VariableSymbol& symbol;

    explicit VariableDeclStatement(const VariableSymbol& symbol) :
        Statement(StatementKind::VariableDeclaration), symbol(symbol) {}

    bool eval(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::VariableDeclaration; }
};

class ConditionalStatement : public Statement {
public:
    const Expression& cond;
    const Statement& ifTrue;
    const Statement* ifFalse;

    ConditionalStatement(const Expression& cond, const Statement& ifTrue,
                         const Statement* ifFalse) :
        Statement(StatementKind::Conditional),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse) {}

    bool eval(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ConditionalStatementSyntax& syntax,
                                 const BindContext& context, BlockList& blocks);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Conditional; }
};

class ForLoopStatement : public Statement {
public:
    const StatementList& initializers;
    const Expression* stopExpr;
    span<const Expression* const> steps;
    const Statement& body;

    ForLoopStatement(const StatementList& initializers, const Expression* stopExpr,
                     span<const Expression* const> steps, const Statement& body) :
        Statement(StatementKind::ForLoop),
        initializers(initializers), stopExpr(stopExpr), steps(steps), body(body) {}

    bool eval(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForLoopStatementSyntax& syntax,
                                 const BindContext& context, BlockList& blocks);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForLoop; }
};

class ExpressionStatement : public Statement {
public:
    const Expression& expr;

    explicit ExpressionStatement(const Expression& expr) :
        Statement(StatementKind::ExpressionStatement), expr(expr) {}

    bool eval(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ExpressionStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }
};

} // namespace slang