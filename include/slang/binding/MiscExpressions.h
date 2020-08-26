//------------------------------------------------------------------------------
//! @file MiscExpressions.h
//! @brief Definitions for miscellaneous expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

/// Represents an expression that references a named value.
class NamedValueExpression : public Expression {
public:
    const ValueSymbol& symbol;
    bool isHierarchical;

    NamedValueExpression(const ValueSymbol& symbol, bool isHierarchical, SourceRange sourceRange) :
        Expression(ExpressionKind::NamedValue, symbol.getType(), sourceRange), symbol(symbol),
        isHierarchical(isHierarchical) {}

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;
    bool verifyAssignableImpl(const BindContext& context, bool isNonBlocking,
                              SourceLocation location) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSymbol(const BindContext& context, const Symbol& symbol,
                                  bool isHierarchical, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NamedValue; }
};

/// Represents a subroutine call.
class CallExpression : public Expression {
public:
    struct SystemCallInfo {
        not_null<const SystemSubroutine*> subroutine;
        not_null<const Scope*> scope;
    };

    using Subroutine = std::variant<const SubroutineSymbol*, SystemCallInfo>;
    Subroutine subroutine;

    CallExpression(const Subroutine& subroutine, const Type& returnType,
                   span<const Expression*> arguments, LookupLocation lookupLocation,
                   SourceRange sourceRange) :
        Expression(ExpressionKind::Call, returnType, sourceRange),
        subroutine(subroutine), arguments_(arguments), lookupLocation(lookupLocation) {}

    span<const Expression* const> arguments() const { return arguments_; }
    span<const Expression*> arguments() { return arguments_; }

    bool isSystemCall() const { return subroutine.index() == 1; }

    string_view getSubroutineName() const;
    SubroutineKind getSubroutineKind() const;

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const InvocationExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                  const InvocationExpressionSyntax* syntax, SourceRange range,
                                  const BindContext& context);

    static Expression& fromSystemMethod(Compilation& compilation, const Expression& expr,
                                        const LookupResult::MemberSelector& selector,
                                        const InvocationExpressionSyntax* syntax,
                                        const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Call; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto arg : arguments())
            arg->visit(visitor);
    }

private:
    static Expression& createSystemCall(Compilation& compilation,
                                        const SystemSubroutine& subroutine,
                                        const Expression* firstArg,
                                        const InvocationExpressionSyntax* syntax, SourceRange range,
                                        const BindContext& context);

    static bool checkConstant(EvalContext& context, const SubroutineSymbol& subroutine,
                              SourceRange range);

    span<const Expression*> arguments_;
    LookupLocation lookupLocation;
};

/// Adapts a data type for use in an expression tree. This is for cases where both an expression
/// and a data type is valid; for example, as an argument to a $bits() call or as a parameter
/// assignment (because of type parameters).
class DataTypeExpression : public Expression {
public:
    DataTypeExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::DataType, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer&) const {}

    static Expression& fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::DataType; }
};

/// Adapts a hierarchical symbol reference for use in an expression tree. This is for cases
/// like the $printtimescale system function that require a module name to be passed.
/// Note that the type of this expression is always void.
class HierarchicalReferenceExpression : public Expression {
public:
    not_null<const Symbol*> symbol;

    HierarchicalReferenceExpression(const Symbol& symbol, const Type& type,
                                    SourceRange sourceRange) :
        Expression(ExpressionKind::HierarchicalReference, type, sourceRange),
        symbol(&symbol) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NameSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::HierarchicalReference;
    }
};

/// Represents an empty argument. There's no actual syntax to go along with this,
/// but we use this as a placeholder to hold the fact that the argument is empty.
class EmptyArgumentExpression : public Expression {
public:
    EmptyArgumentExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::EmptyArgument, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::EmptyArgument; }
};

struct MinTypMaxExpressionSyntax;

/// Represents a min:typ:max expression.
class MinTypMaxExpression : public Expression {
public:
    MinTypMaxExpression(const Type& type, Expression& min, Expression& typ, Expression& max,
                        Expression* selected, SourceRange sourceRange) :
        Expression(ExpressionKind::MinTypMax, type, sourceRange),
        selected_(selected), min_(&min), typ_(&typ), max_(&max) {}

    const Expression& min() const { return *min_; }
    Expression& min() { return *min_; }

    const Expression& typ() const { return *typ_; }
    Expression& typ() { return *typ_; }

    const Expression& max() const { return *max_; }
    Expression& max() { return *max_; }

    const Expression& selected() const { return *selected_; }
    Expression& selected() { return *selected_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const BindContext& context, const Type& newType);
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const MinTypMaxExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MinTypMax; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        // This only visits the selected expression... you could imagine
        // wanting to visit all three instead though.
        selected().visit(visitor);
    }

private:
    Expression* selected_;
    Expression* min_;
    Expression* typ_;
    Expression* max_;
};

} // namespace slang
