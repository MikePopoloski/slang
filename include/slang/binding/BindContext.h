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
    IntegralConstant = 2,
    InsideConcatenation = 4,
    AllowDataType = 8
};
BITMASK_DEFINE_MAX_ELEMENT(BindFlags, AllowDataType);

struct BindContext {
    const Scope& scope;
    LookupNameKind lookupKind = LookupNameKind::Variable;
    LookupLocation lookupLocation;
    bitmask<BindFlags> flags;

    BindContext(const Scope& scope, LookupLocation lookupLocation, bitmask<BindFlags> flags = BindFlags::None) :
        scope(scope), lookupLocation(lookupLocation), flags(flags) {}

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    bool checkLValue(const Expression& expr, SourceLocation location) const;
    bool checkNoUnknowns(const SVInt& value, SourceRange range) const;
    bool checkPositive(const SVInt& value, SourceRange range) const;
    optional<bitwidth_t> checkValidBitWidth(const SVInt& value, SourceRange range) const;

    bool isConstant() const {
        return (flags & BindFlags::Constant) || (flags & BindFlags::IntegralConstant);
    }

    BindContext resetFlags(bitmask<BindFlags> addedFlags) const;
};

}