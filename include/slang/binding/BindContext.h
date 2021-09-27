//------------------------------------------------------------------------------
//! @file BindContext.h
//! @brief Expression binding context
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <tuple>

#include "slang/binding/Lookup.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/util/Util.h"

namespace slang {

class Compilation;
class EvalContext;
class Expression;
class InstanceSymbolBase;
class IteratorSymbol;
class Scope;
class Statement;
class Type;
class VariableSymbol;
struct AttributeInstanceSyntax;
struct ExpressionSyntax;
struct PropertyExprSyntax;
struct SelectorSyntax;
struct VariableDimensionSyntax;
enum class RandMode;

/// Specifies flags that control expression and statement binding.
enum class BindFlags {
    /// No special binding behavior specified.
    None = 0,

    /// The binding is for a constant expression, so report an error if
    /// it's not constant for some reason.
    Constant = 1 << 0,

    /// No hierarchical references are allowed to symbols. This is implied by
    /// @a Constant but can be specified on its own if the expression doesn't
    /// need to be fully constant.
    NoHierarchicalNames = 1 << 1,

    /// The expression is inside a concatenation; this enables slightly
    /// different binding rules.
    InsideConcatenation = 1 << 2,

    /// The expression is inside the unevaluated side of a conditional branch.
    /// This is used to avoid issuing warnings for things that won't happen.
    UnevaluatedBranch = 1 << 3,

    /// Allow the expression to also be a data type; used in a few places like
    /// the first argument to system methods like $bits
    AllowDataType = 1 << 4,

    /// The expression being bound is an enum value initializer.
    EnumInitializer = 1 << 5,

    /// Attributes are disallowed on expressions in this context.
    NoAttributes = 1 << 6,

    /// Assignment is allowed in this context. This flag is cleared
    /// for nested subexpressions, unless they are directly parenthesized.
    AssignmentAllowed = 1 << 7,

    /// Assignments are disallowed in this context. As opposed to the AssignmentAllowed
    /// flag, this is not cleared and overrides that fact even if we are in a
    /// procedural context and would otherwise be allowed to modify variables.
    AssignmentDisallowed = 1 << 8,

    /// Expression is not inside a procedural context.
    NonProcedural = 1 << 9,

    /// Expression is for a static variable's initializer. References to automatic
    /// variables will be disallowed.
    StaticInitializer = 1 << 10,

    /// Streaming operator is allowed in assignment target, assignment source, bit-stream casting
    /// argument, or stream expressions of another streaming concatenation. This flag is cleared for
    /// nested subexpressions, unless they are directly parenthesized.
    StreamingAllowed = 1 << 11,

    /// This is the first expression appearing as an expression statement; potentially this
    /// indicates whether a subroutine invocation is as a task (if set) or as a function (unset).
    /// Cleared for nested subexpressions.
    TopLevelStatement = 1 << 12,

    /// Expression is allowed to be the unbounded literal '$' such as inside a queue select.
    AllowUnboundedLiteral = 1 << 13,

    /// Expression is allowed to do arithmetic with an unbounded literal.
    AllowUnboundedLiteralArithmetic = 1 << 14,

    /// Specparams are allowed even if this is also a constant expression.
    SpecparamsAllowed = 1 << 15,

    /// Binding is happening within a function body
    Function = 1 << 16,

    /// Binding is happening within a final block.
    Final = 1 << 17,

    /// Binding is happening within the intra-assignment timing control of
    /// a non-blocking assignment expression.
    NonBlockingTimingControl = 1 << 18,

    /// Binding is happening within an event expression.
    EventExpression = 1 << 19,

    /// Binding is in a context where type reference expressions are allowed.
    AllowTypeReferences = 1 << 20,

    /// Binding is happening within an assertion expression (sequence or property).
    AssertionExpr = 1 << 21,

    /// Allow binding a clocking block as part of a top-level event expression.
    AllowClockingBlock = 1 << 22,

    /// Binding is for checking an assertion argument, prior to it being expanded as
    /// part of an actual instance.
    AssertionInstanceArgCheck = 1 << 23,

    /// Binding is for a cycle delay or sequence repetition, where references to
    /// assertion formal ports have specific type requirements.
    AssertionDelayOrRepetition = 1 << 24,

    /// Binding is for the left hand side of an assignment operation.
    LValue = 1 << 25,

    /// Binding is for the negation of a property, which disallows recursive
    /// instantiations.
    PropertyNegation = 1 << 26,

    /// Binding is for a property that has come after a positive advancement
    /// of time within the parent property definition.
    PropertyTimeAdvance = 1 << 27,

    /// Binding is for an argument passed to a recursive property instance.
    RecursivePropertyArg = 1 << 28,

    /// Binding is inside a concurrent assertion's action block.
    ConcurrentAssertActionBlock = 1 << 29
};
BITMASK(BindFlags, ConcurrentAssertActionBlock);

enum class DimensionKind { Unknown, Range, AbbreviatedRange, Dynamic, Associative, Queue };

struct EvaluatedDimension {
    DimensionKind kind = DimensionKind::Unknown;
    ConstantRange range;
    const Type* associativeType = nullptr;
    uint32_t queueMaxSize = 0;

    bool isRange() const {
        return kind == DimensionKind::Range || kind == DimensionKind::AbbreviatedRange;
    }
};

/// Contains required context for binding syntax nodes with symbols to form
/// an AST. Expressions, statements, timing controls, constraints, and assertion
/// items all use this for binding.
class BindContext {
public:
    /// The scope where the binding is occurring.
    not_null<const Scope*> scope;

    /// The location to use when looking up names during binding.
    SymbolIndex lookupIndex;

    /// Various flags that control how binding is performed.
    bitmask<BindFlags> flags;

    /// An optional pointer to the context used by an active expression evaluation.
    /// If this is set, it means that the binding was forced by the evaluation and
    /// we can use that information for more informative error messages.
    EvalContext* evalContext = nullptr;

    /// If the expression being bound is for an instance port connection, this is
    /// a pointer to that instance; otherwise, it's nullptr.
    const InstanceSymbolBase* instance = nullptr;

    /// If an array iteration expression is being bound, this contains the symbol
    /// representing the first iterator, along with a linked list of any others
    /// that may be active.
    const IteratorSymbol* firstIterator = nullptr;

    /// A collection of information needed to bind names inside inline constraint
    /// blocks for class and scope randomize function calls.
    struct RandomizeDetails {
        /// The scope of the class type itself, if randomizing a class.
        const Scope* classType = nullptr;

        /// A list of names to which class-scoped lookups are restricted.
        /// If empty, the lookup is unrestricted and all names are first
        /// tried in class-scope.
        span<const string_view> nameRestrictions;

        /// A set of variables for a scope randomize call that should be
        /// treated as a rand variable.
        flat_hash_set<const Symbol*> scopeRandVars;
    };

    /// If this context is for binding an inline constraint block for a randomize
    /// function call, this points to information about the scope. Name lookups
    /// happen inside the class scope before going through the normal local lookup,
    /// for example.
    const RandomizeDetails* randomizeDetails = nullptr;

    /// Information required to instantiate a sequence or property instance.
    struct AssertionInstanceDetails {
        /// The assertion member being instantiated.
        const Symbol* symbol = nullptr;

        /// The previous binding context used to start the instantiation.
        /// This effectively forms a linked list when expanding a nested
        /// stack of sequence and property instances.
        const BindContext* prevContext = nullptr;

        /// The location where the instance is being instantiated.
        SourceLocation instanceLoc;

        /// A map of formal argument symbols to their actual replacements.
        flat_hash_map<const Symbol*, std::tuple<const PropertyExprSyntax*, BindContext>>
            argumentMap;

        /// A map of local variables declared in the assertion item.
        /// These don't exist in any scope because their types can depend
        /// on the expanded arguments.
        flat_hash_map<string_view, const Symbol*> localVars;

        /// If an argument to a sequence or property is being expanded, this
        /// member contains the source location where the argument was referenced.
        SourceLocation argExpansionLoc;

        /// If an argument is being expanded, this is the context in which the
        /// argument was originally being bound (as opposed to where it is being
        /// expanded now).
        const AssertionInstanceDetails* argDetails = nullptr;

        /// Indicates whether this particular instance has already been seen
        /// previously in the stack of assertion instances being expanded.
        /// Only applicable to properties, since this is illegal for sequences.
        bool isRecursive = false;
    };

    /// If this context is for binding an instantiation of a sequence or
    /// property instance this points to information about that instantiation.
    const AssertionInstanceDetails* assertionInstance = nullptr;

    BindContext(const Scope& scope, LookupLocation lookupLocation,
                bitmask<BindFlags> flags = BindFlags::None) :
        scope(&scope),
        lookupIndex(lookupLocation.getIndex()), flags(flags) {
        ASSERT(!lookupLocation.getScope() || lookupLocation.getScope() == &scope);
    }

    Compilation& getCompilation() const;
    LookupLocation getLocation() const { return LookupLocation(scope, uint32_t(lookupIndex)); }
    bool inUnevaluatedBranch() const { return (flags & BindFlags::UnevaluatedBranch) != 0; }
    bool isPortConnection() const;

    void setAttributes(const Statement& stmt,
                       span<const AttributeInstanceSyntax* const> syntax) const;

    void setAttributes(const Expression& expr,
                       span<const AttributeInstanceSyntax* const> syntax) const;

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    bool requireIntegral(const ConstantValue& cv, SourceRange range) const;
    bool requireNoUnknowns(const SVInt& value, SourceRange range) const;
    bool requirePositive(const SVInt& value, SourceRange range) const;
    bool requirePositive(optional<int32_t> value, SourceRange range) const;
    bool requireGtZero(optional<int32_t> value, SourceRange range) const;
    bool requireBooleanConvertible(const Expression& expr) const;
    bool requireAssignable(const VariableSymbol& var, bool isNonBlocking, SourceLocation assignLoc,
                           SourceRange varRange) const;
    bool requireValidBitWidth(bitwidth_t width, SourceRange range) const;
    optional<bitwidth_t> requireValidBitWidth(const SVInt& value, SourceRange range) const;

    ConstantValue eval(const Expression& expr) const;
    ConstantValue tryEval(const Expression& expr) const;

    optional<int32_t> evalInteger(const ExpressionSyntax& syntax,
                                  bitmask<BindFlags> extraFlags = {}) const;
    optional<int32_t> evalInteger(const Expression& expr) const;
    EvaluatedDimension evalDimension(const VariableDimensionSyntax& syntax, bool requireRange,
                                     bool isPacked) const;

    optional<ConstantRange> evalPackedDimension(const VariableDimensionSyntax& syntax) const;
    optional<ConstantRange> evalPackedDimension(const ElementSelectSyntax& syntax) const;
    optional<ConstantRange> evalUnpackedDimension(const VariableDimensionSyntax& syntax) const;

    /// Subroutine argument expressions are parsed as property expressions, since we don't know
    /// up front whether they will be used to instantiate a property or a sequence or are actually
    /// for a subroutine. This method unwraps for the case where we are calling a subroutine.
    const ExpressionSyntax* requireSimpleExpr(const PropertyExprSyntax& expr) const;
    const ExpressionSyntax* requireSimpleExpr(const PropertyExprSyntax& expr, DiagCode code) const;

    /// Gets the rand mode for the given symbol, taking into account any randomize
    /// scope that may be active in this context.
    RandMode getRandMode(const Symbol& symbol) const;

    /// If this context is within an assertion instance, report a backtrace of how that
    /// instance was expanded to the given diagnostic; otherwise, do nothing.
    void addAssertionBacktrace(Diagnostic& diag) const;

    BindContext resetFlags(bitmask<BindFlags> addedFlags) const;

private:
    void evalRangeDimension(const SelectorSyntax& syntax, bool isPacked,
                            EvaluatedDimension& result) const;
};

} // namespace slang
