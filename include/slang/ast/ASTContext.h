//------------------------------------------------------------------------------
//! @file ASTContext.h
//! @brief AST creation context
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <tuple>

#include "slang/ast/Lookup.h"
#include "slang/ast/Scope.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Hash.h"
#include "slang/util/Util.h"

namespace slang::ast {

class Expression;
class InstanceSymbolBase;
class ProceduralBlockSymbol;
class Statement;
class SubroutineSymbol;
class TempVarSymbol;
class Type;
class ValueSymbol;
enum class RandMode;

/// Specifies flags that control expression and statement creation.
enum class SLANG_EXPORT ASTFlags : uint64_t {
    /// No special behavior specified.
    None = 0,

    /// The expression is inside a concatenation; this enables slightly
    /// different creation rules.
    InsideConcatenation = 1ull << 0,

    /// The expression is inside the unevaluated side of a conditional branch.
    /// This is used to avoid issuing warnings for things that won't happen.
    UnevaluatedBranch = 1ull << 1,

    /// Allow the expression to also be a data type; used in a few places like
    /// the first argument to system methods like $bits
    AllowDataType = 1ull << 2,

    /// Assignment is allowed in this context. This flag is cleared
    /// for nested subexpressions, unless they are directly parenthesized.
    AssignmentAllowed = 1ull << 3,

    /// Assignments are disallowed in this context. As opposed to the AssignmentAllowed
    /// flag, this is not cleared and overrides that fact even if we are in a
    /// procedural context and would otherwise be allowed to modify variables.
    AssignmentDisallowed = 1ull << 4,

    /// Expression is not inside a procedural context.
    NonProcedural = 1ull << 5,

    /// Expression is for a static variable's initializer. References to automatic
    /// variables will be disallowed.
    StaticInitializer = 1ull << 6,

    /// Streaming operator is allowed in assignment target, assignment source, bit-stream casting
    /// argument, or stream expressions of another streaming concatenation. This flag is cleared for
    /// nested subexpressions, unless they are directly parenthesized.
    StreamingAllowed = 1ull << 7,

    /// This is the first expression appearing as an expression statement; potentially this
    /// indicates whether a subroutine invocation is as a task (if set) or as a function (unset).
    /// Cleared for nested subexpressions.
    TopLevelStatement = 1ull << 8,

    /// Expression is allowed to be the unbounded literal '$' such as inside a queue select.
    AllowUnboundedLiteral = 1ull << 9,

    /// Expression is allowed to do arithmetic with an unbounded literal.
    AllowUnboundedLiteralArithmetic = 1ull << 10,

    /// AST creation is happening within a function body
    Function = 1ull << 11,

    /// AST creation is happening within a final block.
    Final = 1ull << 12,

    /// AST creation is happening within the intra-assignment timing control of
    /// a non-blocking assignment expression.
    NonBlockingTimingControl = 1ull << 13,

    /// AST creation is happening within an event expression.
    EventExpression = 1ull << 14,

    /// AST creation is in a context where type reference expressions are allowed.
    AllowTypeReferences = 1ull << 15,

    /// AST creation is happening within an assertion expression (sequence or property).
    AssertionExpr = 1ull << 16,

    /// Allow binding a clocking block as part of a top-level event expression.
    AllowClockingBlock = 1ull << 17,

    /// AST creation is for checking an assertion argument, prior to it being expanded as
    /// part of an actual instance.
    AssertionInstanceArgCheck = 1ull << 18,

    /// AST creation is for a cycle delay or sequence repetition, where references to
    /// assertion formal ports have specific type requirements.
    AssertionDelayOrRepetition = 1ull << 19,

    /// AST creation is for the left hand side of an assignment operation.
    LValue = 1ull << 20,

    /// AST creation is for the negation of a property, which disallows recursive
    /// instantiations.
    PropertyNegation = 1ull << 21,

    /// AST creation is for a property that has come after a positive advancement
    /// of time within the parent property definition.
    PropertyTimeAdvance = 1ull << 22,

    /// AST creation is for an argument passed to a recursive property instance.
    RecursivePropertyArg = 1ull << 23,

    /// AST creation is inside a concurrent assertion's action block.
    ConcurrentAssertActionBlock = 1ull << 24,

    /// AST creation is for a covergroup expression that permits referencing a
    /// formal argument of an overridden sample method.
    AllowCoverageSampleFormal = 1ull << 25,

    /// Expressions are allowed to reference coverpoint objects directly.
    AllowCoverpoint = 1ull << 26,

    /// User-defined nettypes are allowed to be looked up in this context.
    AllowNetType = 1ull << 27,

    /// AST creation is for an output (or inout) port or function argument.
    OutputArg = 1ull << 28,

    /// AST creation is for a procedural assign statement.
    ProceduralAssign = 1ull << 29,

    /// AST creation is for a procedural force / release / deassign statement.
    ProceduralForceRelease = 1ull << 30,

    /// AST creation is in a context that allows interconnect nets.
    AllowInterconnect = 1ull << 31,

    /// AST creation is in a context where drivers should not be registered for
    /// lvalues, even if they otherwise would normally be. This is used, for example,
    /// in potentially unrollable for loops to let the loop unroller handle the drivers.
    NotADriver = 1ull << 32,

    /// AST creation is for a range expression inside a streaming concatenation operator.
    StreamingWithRange = 1ull << 33,

    /// AST creation is happening inside a specify block.
    SpecifyBlock = 1ull << 34,

    /// AST creation is for a specparam initializer expression.
    SpecparamInitializer = 1ull << 35,

    /// AST creation is for a DPI argument type.
    DPIArg = 1ull << 36,

    /// AST creation is for an assertion instance's default argument.
    AssertionDefaultArg = 1ull << 37,

    /// AST creation is for an lvalue that also counts as an rvalue. Only valid
    /// when combined with the LValue flag -- used for things like the pre & post
    /// increment and decrement operators.
    LAndRValue = 1ull << 38,

    /// AST binding should not count symbol references towards that symbol being "used".
    /// If this flag is not set, accessing a variable or net in an expression will count
    /// that symbol as being "used".
    NoReference = 1ull << 39,

    /// AST binding is for a parameter inside a SystemVerilog configuration.
    ConfigParam = 1ull << 40,

    /// AST binding is for the contents of the type() operator.
    TypeOperator = 1ull << 41,

    /// AST binding is inside a fork-join_any or fork-join_none block.
    ForkJoinAnyNone = 1ull << 42,

    /// AST binding disallows nets with a user-defined nettype (UDNT).
    DisallowUDNT = 1ull << 43,

    /// AST binding is for a bind instantiation (port connection or param value).
    BindInstantiation = 1ull << 44,
};
SLANG_BITMASK(ASTFlags, BindInstantiation)

// clang-format off
#define DK(x) \
    x(Unknown) \
    x(Range) \
    x(AbbreviatedRange) \
    x(Dynamic) \
    x(Associative) \
    x(Queue) \
    x(DPIOpenArray)
// clang-format on
SLANG_ENUM(DimensionKind, DK)
#undef DK

/// Various flags that can be applied to a constant expression evaluation.
enum class SLANG_EXPORT EvalFlags : uint8_t {
    /// No special flags specified.
    None = 0,

    /// This evaluation is happening inside of a script, so some
    /// language rules should be relaxed.
    IsScript = 1 << 0,

    /// The results of the evaluation can be cached in each expression's
    /// `constant` pointer.
    CacheResults = 1 << 1,

    /// Specparams are allowed during evaluation.
    SpecparamsAllowed = 1 << 2,

    /// Evaluation is for a covergroup expression, which allows some
    /// forms of non-constant variables to be referenced.
    CovergroupExpr = 1 << 3,

    /// For parameter evaluation, allow unbounded literals to evaluate to
    /// the placeholder value. Other expressions that have an unbounded literal
    /// without a queue target will return an invalid value.
    AllowUnboundedPlaceholder = 1 << 4
};
SLANG_BITMASK(EvalFlags, AllowUnboundedPlaceholder)

/// The result of evaluating dimension syntax nodes.
struct SLANG_EXPORT EvaluatedDimension {
    /// The kind of dimension indicated by the syntax nodes.
    DimensionKind kind = DimensionKind::Unknown;

    /// The compile-time constant range specifying the dimensions.
    ConstantRange range;

    /// If the dimension is for an associative type, this is a pointer to that type.
    /// Otherwise nullptr.
    const Type* associativeType = nullptr;

    /// If the dimension is for a queue type, this is the optionally specified
    /// max queue size.
    uint32_t queueMaxSize = 0;

    /// Indicates whether the dimension is for a range (as opposed to a single
    /// index or an associative array access, for example).
    bool isRange() const {
        return kind == DimensionKind::Range || kind == DimensionKind::AbbreviatedRange;
    }
};

/// Information required to instantiate a sequence, property, or checker instance.
struct SLANG_EXPORT AssertionInstanceDetails {
    /// The assertion member being instantiated.
    const Symbol* symbol = nullptr;

    /// The previous AST context used to start the instantiation.
    /// This effectively forms a linked list when expanding a nested
    /// stack of sequence and property instances.
    const ASTContext* prevContext = nullptr;

    /// The location where the instance is being instantiated.
    SourceLocation instanceLoc;

    /// A map of formal argument symbols to their actual replacements.
    flat_hash_map<const Symbol*, std::tuple<const syntax::PropertyExprSyntax*, ASTContext>>
        argumentMap;

    /// A map of local variables declared in the assertion item.
    /// These don't exist in any scope because their types can depend
    /// on the expanded arguments.
    flat_hash_map<std::string_view, const Symbol*> localVars;

    /// If an argument to a sequence or property is being expanded, this
    /// member contains the source location where the argument was referenced.
    SourceLocation argExpansionLoc;

    /// If an argument is being expanded, this is the context in which the
    /// argument was originally being created (as opposed to where it is being
    /// expanded now).
    const AssertionInstanceDetails* argDetails = nullptr;

    /// Indicates whether this particular instance has already been seen
    /// previously in the stack of assertion instances being expanded.
    /// Only applicable to properties, since this is illegal for sequences.
    bool isRecursive = false;
};

/// @brief Contains required context for binding syntax nodes with symbols to form
/// an AST.
///
/// Expressions, statements, timing controls, constraints, and assertion
/// items all use this for creation.
class SLANG_EXPORT ASTContext {
public:
    /// The scope where the AST creation is occurring.
    not_null<const Scope*> scope;

    /// The location to use when looking up names.
    SymbolIndex lookupIndex;

    /// Various flags that control how AST creation is performed.
    bitmask<ASTFlags> flags;

private:
    const Symbol* instanceOrProc = nullptr;

public:
    /// If any temporary variables have been materialized in this context,
    /// contains a pointer to the first one along with a linked list of any
    /// others that may be active. Otherwise nullptr.
    const TempVarSymbol* firstTempVar = nullptr;

    /// A collection of information needed to bind names inside inline constraint
    /// blocks for class and scope randomize function calls.
    struct RandomizeDetails {
        /// The scope of the class type itself, if randomizing a class.
        const Scope* classType = nullptr;

        /// If randomizing a class via a dotted handle access, this is
        /// the the class handle symbol.
        const Symbol* thisVar = nullptr;

        /// A list of names to which class-scoped lookups are restricted.
        /// If empty, the lookup is unrestricted and all names are first
        /// tried in class-scope.
        std::span<const std::string_view> nameRestrictions;

        /// A set of variables for a scope randomize call that should be
        /// treated as a rand variable.
        flat_hash_set<const Symbol*> scopeRandVars;
    };

    /// If this context is for creating an inline constraint block for a randomize
    /// function call, this points to information about the scope. Name lookups
    /// happen inside the class scope before going through the normal local lookup,
    /// for example.
    const RandomizeDetails* randomizeDetails = nullptr;

    /// If this context is for creating an instantiation of a sequence or
    /// property this points to information about that instantiation.
    const AssertionInstanceDetails* assertionInstance = nullptr;

    /// Constructs a new ASTContext instance.
    /// @param scope The scope in which the AST is being created
    /// @param lookupLocation The lookup location within the parent
    ///                       scope where lookups are being performed.
    /// @param flags Flags that control AST creation
    ASTContext(const Scope& scope, LookupLocation lookupLocation,
               bitmask<ASTFlags> flags = ASTFlags::None) :
        scope(&scope), lookupIndex(lookupLocation.getIndex()), flags(flags) {
        SLANG_ASSERT(!lookupLocation.getScope() || lookupLocation.getScope() == &scope);
    }

    /// Gets the parent compilation associated with the AST.
    Compilation& getCompilation() const { return scope->getCompilation(); }

    /// Gets the lookup location passed to the ASTContext constructor.
    LookupLocation getLocation() const { return LookupLocation(scope, uint32_t(lookupIndex)); }

    /// Indicates whether the AST creation is happening inside an unevaluated branch.
    bool inUnevaluatedBranch() const { return flags.has(ASTFlags::UnevaluatedBranch); }

    /// Indicates the kind of driver that each assignment expression created
    /// using this context should use.
    DriverKind getDriverKind() const;

    /// Gets the parent instance if this context is being used to bind expressions
    /// for an instantiation.
    const InstanceSymbolBase* getInstance() const;

    /// If this context is within a procedural block, returns a pointer
    /// to that symbol.
    const ProceduralBlockSymbol* getProceduralBlock() const;

    /// If this context is within a subroutine, returns a pointer to that subroutine.
    const SubroutineSymbol* getContainingSubroutine() const;

    /// Indicates whether AST creation is happening within an always_comb
    /// or always_latch procedure.
    bool inAlwaysCombLatch() const;

    /// Sets the parent instance associated with the context.
    void setInstance(const InstanceSymbolBase& inst);

    /// Sets the procedural block associated with the context.
    void setProceduralBlock(const ProceduralBlockSymbol& block);

    /// Clears the parent instance and parent procedural block symbol
    /// associated with the context.
    void clearInstanceAndProc() { instanceOrProc = nullptr; }

    /// Tries to fill the @a assertionInstance member by searching upward through
    /// parent scopes to find an assertion instantiation.
    /// @returns The nearest parent instantiation, instance body or checker instance,
    ///          or nullptr if neither is found.
    const Symbol* tryFillAssertionDetails();

    /// Registers attributes for the given statement.
    void setAttributes(const Statement& stmt,
                       std::span<const syntax::AttributeInstanceSyntax* const> syntax) const;

    /// Registers attributes for the given expression.
    void setAttributes(const Expression& expr,
                       std::span<const syntax::AttributeInstanceSyntax* const> syntax) const;

    /// Registers a driver for the given symbol.
    /// @param symbol The symbol that is being driven
    /// @param longestStaticPrefix The portion of the symbol that is being driven
    /// @param assignFlags Flags that specify how the driver functions
    void addDriver(const ValueSymbol& symbol, const Expression& longestStaticPrefix,
                   bitmask<AssignFlags> assignFlags) const;

    /// @brief Gets the symbol that contains the AST context
    ///
    /// @returns Either a parent procedural block or subroutine if one is
    /// registered, and if not the scope passed to the ASTContext constructor.
    const Symbol& getContainingSymbol() const;

    /// Issues a new diagnostic.
    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;

    /// Issues a new diagnostic.
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    /// Reports an error if the given expression is not integral.
    /// @returns true if the expression is integral and false otherwise
    bool requireIntegral(const Expression& expr) const;

    /// Reports an error if the given constant value is not integral.
    /// @returns true if the value is integral and false otherwise
    bool requireIntegral(const ConstantValue& cv, SourceRange range) const;

    /// Reports an error if the given integer has unknowns.
    /// @returns false if the value has unknowns and true otherwise
    bool requireNoUnknowns(const SVInt& value, SourceRange range) const;

    /// Reports an error if the given integer is not positive or zero.
    /// @returns true if the value is positive or zero and false otherwise
    bool requirePositive(const SVInt& value, SourceRange range) const;

    /// @brief Reports an error if the given integer is not positive or zero.
    ///
    /// If @a value is unset, this method does not report an error.
    /// @returns true if the value is set and positive or zero and false otherwise
    bool requirePositive(std::optional<int32_t> value, SourceRange range) const;

    /// @brief Reports an error if the given integer is not greater than zero.
    ///
    /// If @a value is unset, this method does not report an error.
    /// @returns true if the value is set and greater than zero and false otherwise
    bool requireGtZero(std::optional<int32_t> value, SourceRange range) const;

    /// Reports an error if the given expression's type is not boolean convertible.
    /// @returns true if the expression is boolean convertible and false otherwise
    bool requireBooleanConvertible(const Expression& expr) const;

    /// Reports an error if the given width is a valid bit width.
    /// @returns true if the width is valid as a bit width and false otherwise
    bool requireValidBitWidth(bitwidth_t width, SourceRange range) const;

    /// Reports an error if time-controlling statements are not allowed in this context.
    /// @returns true if time-controlling statements are allowed and false otherwise
    bool requireTimingAllowed(SourceRange range) const;

    /// Reports an error if the given width is a valid bit width.
    /// @returns A bitwidth if the provided integer is a valid bit width,
    ///          and std::nullopt otherwise.
    std::optional<bitwidth_t> requireValidBitWidth(const SVInt& value, SourceRange range) const;

    /// @brief Evaluates the provided expression as a constant expression.
    ///
    /// If evaluation fails appropriate diagnostics will be issued.
    /// @returns The result of constant evaluation or an empty value if it failed
    ConstantValue eval(const Expression& expr, bitmask<EvalFlags> extraFlags = {}) const;

    /// @brief Evaluates the provided expression as a constant expression.
    ///
    /// If evaluation fails no diagnostics will be issued.
    /// @returns The result of constant evaluation or an empty value if it failed
    ConstantValue tryEval(const Expression& expr) const;

    /// @brief Evaluates the provided expression as an integral constant expression.
    ///
    /// If evaluation fails (or if the expression is not integral to begin with)
    /// appropriate diagnostics will be issued.
    ///
    /// @returns The result of constant evaluation or std::nullopt if it failed
    std::optional<int32_t> evalInteger(const syntax::ExpressionSyntax& syntax,
                                       bitmask<ASTFlags> extraFlags = {}) const;

    /// @brief Evaluates the provided expression as an integral constant expression.
    ///
    /// If evaluation fails (or if the expression is not integral to begin with)
    /// appropriate diagnostics will be issued.
    ///
    /// @returns The result of constant evaluation or std::nullopt if it failed
    std::optional<int32_t> evalInteger(const Expression& expr,
                                       bitmask<EvalFlags> extraFlags = {}) const;

    /// Evaluates the given dimension syntax to determine its compile-time
    /// bounds and other properties.
    /// @param syntax The dimension syntax node to evaluate
    /// @param requireRange If true, the dimension syntax must represent a range,
    ///                     as opposed to a single index or other kind of dimension
    /// @param isPacked If true, this dimension should be treated as a packed dimension
    /// @returns Details about the evaluated dimension
    EvaluatedDimension evalDimension(const syntax::VariableDimensionSyntax& syntax,
                                     bool requireRange, bool isPacked) const;

    /// Evaluates the given dimension syntax to determine its compile-time
    /// bounds and other properties.
    /// @param syntax The dimension syntax node to evaluate
    /// @returns Details about the evaluated dimension
    EvaluatedDimension evalPackedDimension(const syntax::VariableDimensionSyntax& syntax) const;

    /// Evaluates the given dimension syntax to determine its compile-time
    /// bounds and other properties.
    /// @param syntax The dimension syntax node to evaluate
    /// @returns Details about the evaluated dimension
    EvaluatedDimension evalPackedDimension(const syntax::ElementSelectSyntax& syntax) const;

    /// Evaluates the given dimension syntax to determine its compile-time
    /// bounds and other properties.
    /// @param syntax The dimension syntax node to evaluate
    /// @returns Details about the evaluated dimension
    EvaluatedDimension evalUnpackedDimension(const syntax::VariableDimensionSyntax& syntax) const;

    /// @brief Checks and unwraps a given property expression syntax node into a
    /// simple expression syntax pointer.
    ///
    /// Subroutine argument expressions are parsed as property expressions, since we don't know
    /// up front whether they will be used to instantiate a property or a sequence or are actually
    /// for a subroutine. This method unwraps for the case where we are calling a subroutine.
    ///
    /// If the given property expression is actually a real sequence or property expression
    /// and not just a plain old expression an appropriate diagnostic will be issued.
    ///
    /// @returns The unwrapped expression if the given syntax node represents a simple
    ///          expression, and nullptr otherwise.
    const syntax::ExpressionSyntax* requireSimpleExpr(const syntax::PropertyExprSyntax& expr) const;

    /// @brief Checks and unwraps a given property expression syntax node into a
    /// simple expression syntax pointer.
    ///
    /// Subroutine argument expressions are parsed as property expressions, since we don't know
    /// up front whether they will be used to instantiate a property or a sequence or are actually
    /// for a subroutine. This method unwraps for the case where we are calling a subroutine.
    ///
    /// If the given property expression is actually a real sequence or property expression
    /// and not just a plain old expression a diagnostic will be issued with the specified @a code
    ///
    /// @returns The unwrapped expression if the given syntax node represents a simple
    ///          expression, and nullptr otherwise.
    const syntax::ExpressionSyntax* requireSimpleExpr(const syntax::PropertyExprSyntax& expr,
                                                      DiagCode code) const;

    /// Gets the rand mode for the given symbol, taking into account any randomize
    /// scope that may be active in this context.
    RandMode getRandMode(const Symbol& symbol) const;

    /// If this context is within an assertion instance, report a backtrace of how that
    /// instance was expanded to the given diagnostic; otherwise, do nothing.
    void addAssertionBacktrace(Diagnostic& diag) const;

    /// Resets the flags for this context; the @a addedFlags will be added to the flag set,
    /// and any non-sticky flags will be removed.
    ASTContext resetFlags(bitmask<ASTFlags> addedFlags) const;

private:
    void evalRangeDimension(const syntax::SelectorSyntax& syntax, bool isPacked,
                            EvaluatedDimension& result) const;
};

} // namespace slang::ast
