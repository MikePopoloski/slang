//------------------------------------------------------------------------------
//! @file MiscExpressions.h
//! @brief Definitions for miscellaneous expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/symbols/ValueSymbol.h"

namespace slang {

class AssertionExpr;
class Constraint;
class TimingControl;

/// Common base class for both NamedValueExpression and HierarchicalValueExpression.
class ValueExpressionBase : public Expression {
public:
    const ValueSymbol& symbol;

    bool verifyAssignableImpl(const BindContext& context, SourceLocation location,
                              bool isNonBlocking, bool inConcat) const;
    optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSymbol(const BindContext& context, const Symbol& symbol,
                                  bool isHierarchical, SourceRange sourceRange,
                                  bool constraintAllowed = false);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::NamedValue || kind == ExpressionKind::HierarchicalValue;
    }

protected:
    ValueExpressionBase(ExpressionKind kind, const ValueSymbol& symbol, SourceRange sourceRange) :
        Expression(kind, symbol.getType(), sourceRange), symbol(symbol) {}
};

/// Represents an expression that references a named value.
class NamedValueExpression : public ValueExpressionBase {
public:
    NamedValueExpression(const ValueSymbol& symbol, SourceRange sourceRange) :
        ValueExpressionBase(ExpressionKind::NamedValue, symbol, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NamedValue; }
};

/// Represents an expression that references a named value via hierarchical path.
class HierarchicalValueExpression : public ValueExpressionBase {
public:
    HierarchicalValueExpression(const ValueSymbol& symbol, SourceRange sourceRange) :
        ValueExpressionBase(ExpressionKind::HierarchicalValue, symbol, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::HierarchicalValue; }
};

struct ArgumentListSyntax;

/// Represents a subroutine call.
class CallExpression : public Expression {
public:
    struct IteratorCallInfo {
        const Expression* iterExpr = nullptr;
        const ValueSymbol* iterVar = nullptr;
    };

    struct RandomizeCallInfo {
        const Constraint* inlineConstraints = nullptr;
        span<const string_view> constraintRestrictions;
    };

    struct SystemCallInfo {
        not_null<const SystemSubroutine*> subroutine;
        not_null<const Scope*> scope;
        std::variant<std::monostate, IteratorCallInfo, RandomizeCallInfo> extraInfo;

        std::pair<const Expression*, const ValueSymbol*> getIteratorInfo() const;
    };

    using Subroutine = std::variant<const SubroutineSymbol*, SystemCallInfo>;
    Subroutine subroutine;

    CallExpression(const Subroutine& subroutine, const Type& returnType,
                   const Expression* thisClass, span<const Expression*> arguments,
                   LookupLocation lookupLocation, SourceRange sourceRange) :
        Expression(ExpressionKind::Call, returnType, sourceRange),
        subroutine(subroutine), thisClass_(thisClass), arguments_(arguments),
        lookupLocation(lookupLocation) {}

    /// If this call is for a class method, returns the expression representing the
    /// class handle on which the method is being invoked. Otherwise returns nullptr.
    const Expression* thisClass() const { return thisClass_; }

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
                                  const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                  const BindContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const ArrayOrRandomizeMethodExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                  const Expression* thisClass,
                                  const InvocationExpressionSyntax* syntax,
                                  const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                  SourceRange range, const BindContext& context);

    static Expression& fromArgs(Compilation& compilation, const Subroutine& subroutine,
                                const Expression* thisClass, const ArgumentListSyntax* argSyntax,
                                SourceRange range, const BindContext& context);

    static Expression& fromSystemMethod(Compilation& compilation, const Expression& expr,
                                        const LookupResult::MemberSelector& selector,
                                        const InvocationExpressionSyntax* syntax,
                                        const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                        const BindContext& context);

    static Expression* fromBuiltInMethod(Compilation& compilation, SymbolKind rootKind,
                                         const Expression& expr,
                                         const LookupResult::MemberSelector& selector,
                                         const InvocationExpressionSyntax* syntax,
                                         const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                         const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Call; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (thisClass())
            thisClass()->visit(visitor);

        for (auto arg : arguments())
            arg->visit(visitor);
    }

private:
    static Expression& fromSyntaxImpl(Compilation& compilation, const ExpressionSyntax& left,
                                      const InvocationExpressionSyntax* invocation,
                                      const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                      const BindContext& context);

    static Expression& createSystemCall(Compilation& compilation,
                                        const SystemSubroutine& subroutine,
                                        const Expression* firstArg,
                                        const InvocationExpressionSyntax* syntax,
                                        const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                        SourceRange range, const BindContext& context,
                                        const Scope* randomizeScope = nullptr);

    static bool checkConstant(EvalContext& context, const SubroutineSymbol& subroutine,
                              SourceRange range);

    const Expression* thisClass_;
    span<const Expression*> arguments_;
    LookupLocation lookupLocation;

    mutable bool inRecursion = false;
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

/// An expression that gets the type of a nested expression using the type() operator.
/// The result is only allowed in a few places in the grammar, namely in comparisons
/// with other type reference expressions.
class TypeReferenceExpression : public Expression {
public:
    const Type& targetType;

    TypeReferenceExpression(const Type& typeRefType, const Type& targetType,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::TypeReference, typeRefType, sourceRange),
        targetType(targetType) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::TypeReference; }
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

/// A placeholder expression that is generated to take the place of one side of
/// a compound assignment expression's binary operator. It indicates to the constant
/// evaluator that it should look on the lvalue stack for the value to use.
class LValueReferenceExpression : public Expression {
public:
    LValueReferenceExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::LValueReference, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::LValueReference; }
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

struct ClockingPropertyExprSyntax;

/// Represents a clocking event expression. This is a special kind of expression that is only
/// allowed with the sampled value system functions and assertion instance arguments.
class ClockingEventExpression : public Expression {
public:
    const TimingControl& timingControl;

    ClockingEventExpression(const Type& type, const TimingControl& timingControl,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::ClockingEvent, type, sourceRange),
        timingControl(timingControl) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return false; }

    static Expression& fromSyntax(const ClockingPropertyExprSyntax& syntax,
                                  const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ClockingEvent; }
};

/// Represents an instance of an assertion item, either a sequence, a property,
/// or a formal argument that is being referenced and expanded.
class AssertionInstanceExpression : public Expression {
public:
    const Symbol& symbol;
    const AssertionExpr& body;
    bool isRecursiveProperty;

    AssertionInstanceExpression(const Type& type, const Symbol& symbol, const AssertionExpr& body,
                                bool isRecursiveProperty, SourceRange sourceRange) :
        Expression(ExpressionKind::AssertionInstance, type, sourceRange),
        symbol(symbol), body(body), isRecursiveProperty(isRecursiveProperty) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return false; }

    static Expression& fromLookup(const Symbol& symbol, const InvocationExpressionSyntax* syntax,
                                  SourceRange range, const BindContext& context);

    static Expression& makeDefault(const Symbol& symbol);

    static Expression& bindPort(const Symbol& symbol, SourceRange range,
                                const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::AssertionInstance; }
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
    optional<bitwidth_t> getEffectiveWidthImpl() const;

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

struct CopyClassExpressionSyntax;

/// Represents a `new` expression that copies a class instance.
class CopyClassExpression : public Expression {
public:
    CopyClassExpression(const Type& type, const Expression& sourceExpr, SourceRange sourceRange) :
        Expression(ExpressionKind::CopyClass, type, sourceRange), sourceExpr_(sourceExpr) {}

    const Expression& sourceExpr() const { return sourceExpr_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const CopyClassExpressionSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::CopyClass; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        sourceExpr().visit(visitor);
    }

private:
    const Expression& sourceExpr_;
};

struct ExpressionOrDistSyntax;

/// Denotes an expression along with a distribution of probabilities for that
/// expression. This can't occur in normal expression code; it's used as part
/// of constraints and properties (and always has the type 'void').
class DistExpression : public Expression {
public:
    struct DistWeight {
        enum Kind { PerValue, PerRange } kind;
        const Expression& expr;
    };

    struct DistItem {
        const Expression& value;
        optional<DistWeight> weight;
    };

    DistExpression(const Type& type, const Expression& left, span<DistItem> items,
                   SourceRange sourceRange) :
        Expression(ExpressionKind::Dist, type, sourceRange),
        left_(&left), items_(items) {}

    const Expression& left() const { return *left_; }
    span<DistItem const> items() const { return items_; }

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }
    bool verifyConstantImpl(EvalContext&) const { return false; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& comp, const ExpressionOrDistSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Dist; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        for (auto& item : items_) {
            item.value.visit(visitor);
            if (item.weight)
                item.weight->expr.visit(visitor);
        }
    }

private:
    const Expression* left_;
    span<DistItem> items_;
};

} // namespace slang
