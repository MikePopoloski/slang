//------------------------------------------------------------------------------
//! @file MiscExpressions.h
//! @brief Definitions for miscellaneous expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

class FieldSymbol;

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

    void toJson(json& j) const;

    static Expression& fromSymbol(const Scope& scope, const Symbol& symbol, bool isHierarchical,
                                  SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NamedValue; }
};

/// Represents a single element selection expression.
class ElementSelectExpression : public Expression {
public:
    ElementSelectExpression(const Type& type, Expression& value, Expression& selector,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::ElementSelect, type, sourceRange),
        value_(&value), selector_(&selector) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& selector() const { return *selector_; }
    Expression& selector() { return *selector_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void toJson(json& j) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const ExpressionSyntax& syntax, SourceRange fullRange,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ElementSelect; }

private:
    Expression* value_;
    Expression* selector_;
};

struct RangeSelectSyntax;

/// Represents a range selection expression.
class RangeSelectExpression : public Expression {
public:
    RangeSelectionKind selectionKind;

    RangeSelectExpression(RangeSelectionKind selectionKind, const Type& type, Expression& value,
                          const Expression& left, const Expression& right,
                          SourceRange sourceRange) :
        Expression(ExpressionKind::RangeSelect, type, sourceRange),
        selectionKind(selectionKind), value_(&value), left_(&left), right_(&right) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& left() const { return *left_; }
    const Expression& right() const { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void toJson(json& j) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const RangeSelectSyntax& syntax, SourceRange fullRange,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::RangeSelect; }

private:
    static ConstantRange getIndexedRange(RangeSelectionKind kind, int32_t l, int32_t r,
                                         bool littleEndian);
    optional<ConstantRange> getRange(EvalContext& context, const ConstantValue& cl,
                                     const ConstantValue& cr) const;

    Expression* value_;
    const Expression* left_;
    const Expression* right_;
};

struct MemberAccessExpressionSyntax;

/// Represents an access of a structure variable's members.
class MemberAccessExpression : public Expression {
public:
    const FieldSymbol& field;

    MemberAccessExpression(const Type& type, Expression& value, const FieldSymbol& field,
                           SourceRange sourceRange) :
        Expression(ExpressionKind::MemberAccess, type, sourceRange),
        field(field), value_(&value) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void toJson(json& j) const;

    static Expression& fromSelector(Compilation& compilation, Expression& expr,
                                    const LookupResult::MemberSelector& selector,
                                    const InvocationExpressionSyntax* invocation,
                                    const BindContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const MemberAccessExpressionSyntax& syntax,
                                  const InvocationExpressionSyntax* invocation,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MemberAccess; }

private:
    Expression* value_;
};

/// Represents a subroutine call.
class CallExpression : public Expression {
public:
    using Subroutine = std::variant<const SubroutineSymbol*, const SystemSubroutine*>;
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

    void toJson(json& j) const;

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

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void toJson(json&) const {}

    static Expression& fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::DataType; }
};

/// Represents an empty argument. There's no actual syntax to go along with this,
/// but we use this as a placeholder to hold the fact that the argument is empty.
class EmptyArgumentExpression : public Expression {
public:
    EmptyArgumentExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::EmptyArgument, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void toJson(json&) const {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::EmptyArgument; }
};

} // namespace slang