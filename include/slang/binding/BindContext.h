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

enum class BindFlags : uint8_t {
    None = 0,
    Constant = 1,
    InsideConcatenation = 2,
    AllowDataType = 4,
    EnumInitializer = 8
};
BITMASK_DEFINE_MAX_ELEMENT(BindFlags, EnumInitializer);

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

    BindContext(const Scope& scope, LookupLocation lookupLocation,
                bitmask<BindFlags> flags = BindFlags::None) :
        scope(scope),
        lookupLocation(lookupLocation), flags(flags) {}

    Compilation& getCompilation() const { return scope.getCompilation(); }

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    bool requireLValue(const Expression& expr, SourceLocation location) const;
    bool requireIntegral(const ConstantValue& cv, SourceRange range) const;
    bool requireNoUnknowns(const SVInt& value, SourceRange range) const;
    bool requirePositive(const SVInt& value, SourceRange range) const;
    bool requireGtZero(optional<int32_t> value, SourceRange range) const;
    bool requireValidBitWidth(bitwidth_t width, SourceRange range) const;
    optional<bitwidth_t> requireValidBitWidth(const SVInt& value, SourceRange range) const;

    optional<int32_t> evalInteger(const ExpressionSyntax& syntax) const;
    optional<int32_t> evalInteger(const Expression& expr) const;
    EvaluatedDimension evalDimension(const VariableDimensionSyntax& syntax,
                                     bool requireRange) const;

    optional<ConstantRange> evalPackedDimension(const VariableDimensionSyntax& syntax) const;
    optional<ConstantRange> evalPackedDimension(const ElementSelectSyntax& syntax) const;

    BindContext resetFlags(bitmask<BindFlags> addedFlags) const;

private:
    void evalRangeDimension(const SelectorSyntax& syntax, EvaluatedDimension& result) const;
};

} // namespace slang