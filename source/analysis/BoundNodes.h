#pragma once

#include "ConstantValue.h"
#include "Symbol.h"

namespace slang {

class TypeSymbol;

enum class BoundNodeKind {
    Unknown,
    Literal,
    Variable,
    UnaryExpression,
    BinaryExpression,
    TernaryExpression,
    NaryExpression,
    SelectExpression,
    AssignmentExpression,
    CallExpression,
    StatementList,
    ReturnStatement,
    VariableDeclaration,
    ConditionalStatement,
    ForLoopStatement,
    ExpressionStatement
};

class BoundNode {
public:
    BoundNodeKind kind;

    BoundNode(BoundNodeKind kind) : kind(kind) {}

	// Not copyable
	BoundNode(const BoundNode&) = delete;
	BoundNode& operator=(const BoundNode&) = delete;

    bool bad() const { return kind == BoundNodeKind::Unknown; }
};

class BoundExpression : public BoundNode {
public:
    const ExpressionSyntax& syntax;
    const TypeSymbol* type;

    BoundExpression(BoundNodeKind kind, const ExpressionSyntax& syntax, const TypeSymbol& type) :
        BoundNode(kind), syntax(syntax), type(&type) {}
};

class BadBoundExpression : public BoundExpression {
public:
    const BoundExpression* child;

    BadBoundExpression(const BoundExpression* child) :
        BoundExpression(BoundNodeKind::Unknown, EmptyLiteral, ErrorTypeSymbol::Default), child(child) {}

private:
	static const LiteralExpressionSyntax EmptyLiteral;
};

class BoundLiteral : public BoundExpression {
public:
    ConstantValue value;

    BoundLiteral(const ExpressionSyntax& syntax, const TypeSymbol& type, const ConstantValue& value) :
        BoundExpression(BoundNodeKind::Literal, syntax, type), value(value) {}

    BoundLiteral(const ExpressionSyntax& syntax, const TypeSymbol& type, ConstantValue&& value) :
        BoundExpression(BoundNodeKind::Literal, syntax, type), value(std::move(value)) {}
};

class BoundVariable : public BoundExpression {
public:
    const VariableSymbol& symbol;

    BoundVariable(const ExpressionSyntax& syntax, const VariableSymbol& symbol) :
        BoundExpression(BoundNodeKind::Variable, syntax, symbol.type()), symbol(symbol) {}
};

class BoundUnaryExpression : public BoundExpression {
public:
    BoundExpression& operand;

    BoundUnaryExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, BoundExpression& operand) :
        BoundExpression(BoundNodeKind::UnaryExpression, syntax, type), operand(operand) {}
};

class BoundBinaryExpression : public BoundExpression {
public:
    BoundExpression& left;
    BoundExpression& right;

    BoundBinaryExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, BoundExpression& left, BoundExpression& right) :
        BoundExpression(BoundNodeKind::BinaryExpression, syntax, type), left(left), right(right) {}
};

/// This is used only for ?:
class BoundTernaryExpression : public BoundExpression {
public:
    BoundExpression& pred;
    BoundExpression& left;
    BoundExpression& right;

    BoundTernaryExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, BoundExpression& pred, BoundExpression& left, BoundExpression& right) :
        BoundExpression(BoundNodeKind::TernaryExpression, syntax, type), pred(pred), left(left), right(right) {}

};

/// Also ternary, but needs to store the kind of the selector
class BoundSelectExpression : public BoundExpression {
public:
    SyntaxKind kind;
    const BoundExpression& expr;
    BoundExpression& left;
    BoundExpression& right;

    BoundSelectExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, SyntaxKind kind, const BoundExpression& expr, BoundExpression& left, BoundExpression& right) :
        BoundExpression(BoundNodeKind::SelectExpression, syntax, type), kind(kind), expr(expr), left(left), right(right) {}

};

class BoundNaryExpression : public BoundExpression {
public:
    ArrayRef<const BoundExpression*> exprs;

    BoundNaryExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, ArrayRef<const BoundExpression*> exprs) :
        BoundExpression(BoundNodeKind::NaryExpression, syntax, type),
        exprs(exprs) {}
};

class BoundAssignmentExpression : public BoundExpression {
public:
    BoundExpression& left;
    BoundExpression& right;

    BoundAssignmentExpression(const ExpressionSyntax& syntax, const TypeSymbol& type, BoundExpression& left, BoundExpression& right) :
        BoundExpression(BoundNodeKind::AssignmentExpression, syntax, type), left(left), right(right) {}
};

class BoundCallExpression : public BoundExpression {
public:
    const SubroutineSymbol& subroutine;
    ArrayRef<const BoundExpression*> arguments;

    BoundCallExpression(const ExpressionSyntax& syntax, const SubroutineSymbol& subroutine, ArrayRef<const BoundExpression*> arguments) :
        BoundExpression(BoundNodeKind::CallExpression, syntax, subroutine.returnType()),
        subroutine(subroutine), arguments(arguments) {}
};

class BoundStatement : public BoundNode {
public:
    const StatementSyntax& syntax;

	explicit BoundStatement(BoundNodeKind kind) :
		BoundNode(kind), syntax(EmptyStatement) {}

    BoundStatement(BoundNodeKind kind, const StatementSyntax& syntax) :
        BoundNode(kind), syntax(syntax) {}

private:
	static const EmptyStatementSyntax EmptyStatement;
};

class BadBoundStatement : public BoundStatement {
public:
    const BoundStatement* child;

    BadBoundStatement(const BoundStatement* child) :
        BoundStatement(BoundNodeKind::Unknown), child(child) {}
};

class BoundStatementList : public BoundStatement {
public:
    ArrayRef<const BoundStatement*> list;

    BoundStatementList(ArrayRef<const BoundStatement*> list) :
        BoundStatement(BoundNodeKind::StatementList), list(list) {}
};

class BoundReturnStatement : public BoundStatement {
public:
    const BoundExpression* expr;

    BoundReturnStatement(const StatementSyntax& syntax, const BoundExpression* expr) :
        BoundStatement(BoundNodeKind::ReturnStatement, syntax), expr(expr) {}
};

class BoundVariableDecl : public BoundStatement {
public:
    const VariableSymbol& symbol;

    BoundVariableDecl(const VariableSymbol& symbol) :
        BoundStatement(BoundNodeKind::VariableDeclaration), symbol(symbol) {}
};

class BoundConditionalStatement : public BoundStatement {
public:
    const BoundExpression& cond;
    const BoundStatement& ifTrue;
    const BoundStatement* ifFalse;

    BoundConditionalStatement(const StatementSyntax& syntax, const BoundExpression& cond,
                              const BoundStatement& ifTrue, const BoundStatement* ifFalse) :
        BoundStatement(BoundNodeKind::ConditionalStatement, syntax),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse) {}
};

class BoundForLoopStatement : public BoundStatement {
public:
    ArrayRef<const BoundVariableDecl*> initializers;
    const BoundExpression& stopExpr;
    ArrayRef<const BoundExpression*> steps;
    const BoundStatement& statement;

    BoundForLoopStatement(const StatementSyntax& syntax, ArrayRef<const BoundVariableDecl*> initializers,
                          const BoundExpression& stopExpr, ArrayRef<const BoundExpression*> steps,
                          const BoundStatement& statement) :
        BoundStatement(BoundNodeKind::ForLoopStatement, syntax),
        initializers(initializers), stopExpr(stopExpr), steps(steps), statement(statement) {}
};

class BoundExpressionStatement : public BoundStatement {
public:
    const BoundExpression& expr;

    BoundExpressionStatement(const ExpressionStatementSyntax& syntax, const BoundExpression& expr) :
        BoundStatement(BoundNodeKind::ExpressionStatement, syntax), expr(expr) {}
};

}
