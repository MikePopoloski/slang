//------------------------------------------------------------------------------
// BindContext.h
// Expression binding context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/util/Util.h"

namespace slang {

class EvalContext;

/// Specifies flags that control expression and statement binding.
enum class BindFlags {
    /// No special binding behavior specified.
    None = 0,

    /// The binding is for a constant expression, so report an error if
    /// it's not constant for some reason.
    Constant = 1,

    /// No hierarchical references are allowed to symbols. This is implied by
    /// @a Constant but can be specified on its own if the expression doesn't
    /// need to be fully constant.
    NoHierarchicalNames = 2,

    /// The expression is inside a concatenation; this enables slightly
    /// different binding rules.
    InsideConcatenation = 4,

    /// Allow the expression to also be a data type; used in a few places like
    /// the first argument to system methods like $bits
    AllowDataType = 8,

    /// The expression being bound is an enum value initializer.
    EnumInitializer = 16,

    /// Attributes are disallowed on expressions in this context.
    NoAttributes = 32
};
BITMASK_DEFINE_MAX_ELEMENT(BindFlags, NoAttributes);

enum class DimensionKind { Unknown, Range, AbbreviatedRange, Dynamic, Associative, Queue };

struct EvaluatedDimension {
    DimensionKind kind = DimensionKind::Unknown;
    ConstantRange range;
    const Type* associativeType = nullptr;
    int32_t queueMaxSize = 0;

    bool isRange() const {
        return kind == DimensionKind::Range || kind == DimensionKind::AbbreviatedRange;
    }
};

class BindContext {
public:
    const Scope& scope;
    LookupLocation lookupLocation;
    bitmask<BindFlags> flags;

    /// An optional pointer to the context used by an active expression evaluation.
    /// If this is set, it means that the binding was forced by the evaluation and
    /// we can use that information for more informative error messages.
    EvalContext* evalContext = nullptr;

    BindContext(const Scope& scope, LookupLocation lookupLocation,
                bitmask<BindFlags> flags = BindFlags::None) :
        scope(scope),
        lookupLocation(lookupLocation), flags(flags) {}

    Compilation& getCompilation() const { return scope.getCompilation(); }

    void addAttributes(const Expression& expr,
                       span<const AttributeInstanceSyntax* const> syntax) const;

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    bool requireLValue(const Expression& expr, SourceLocation location) const;
    bool requireIntegral(const ConstantValue& cv, SourceRange range) const;
    bool requireNoUnknowns(const SVInt& value, SourceRange range) const;
    bool requirePositive(const SVInt& value, SourceRange range) const;
    bool requireGtZero(optional<int32_t> value, SourceRange range) const;
    bool requireBooleanConvertible(const Expression& expr) const;
    bool requireValidBitWidth(bitwidth_t width, SourceRange range) const;
    optional<bitwidth_t> requireValidBitWidth(const SVInt& value, SourceRange range) const;

    optional<int32_t> evalInteger(const ExpressionSyntax& syntax) const;
    optional<int32_t> evalInteger(const Expression& expr) const;
    EvaluatedDimension evalDimension(const VariableDimensionSyntax& syntax,
                                     bool requireRange) const;

    optional<ConstantRange> evalPackedDimension(const VariableDimensionSyntax& syntax) const;
    optional<ConstantRange> evalPackedDimension(const ElementSelectSyntax& syntax) const;
    optional<ConstantRange> evalUnpackedDimension(const VariableDimensionSyntax& syntax) const;

    BindContext resetFlags(bitmask<BindFlags> addedFlags) const;

private:
    void evalRangeDimension(const SelectorSyntax& syntax, EvaluatedDimension& result) const;
};

} // namespace slang