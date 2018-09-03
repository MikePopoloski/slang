//------------------------------------------------------------------------------
// BindContext.cpp
// Expression binding context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/BindContext.h"

#include "slang/binding/Expressions.h"

namespace slang {

Diagnostic& BindContext::addError(DiagCode code, SourceLocation location) const {
    return scope.addError(code, location);
}

Diagnostic& BindContext::addError(DiagCode code, SourceRange sourceRange) const {
    return scope.addError(code, sourceRange);
}

bool BindContext::checkLValue(const Expression& expr, SourceLocation location) const {
    if (!expr.isLValue()) {
        auto& diag = addError(DiagCode::ExpressionNotAssignable, location);
        diag << expr.sourceRange;
        return false;
    }
    return true;
}

bool BindContext::checkNoUnknowns(const SVInt& value, SourceRange range) const {
    if (value.hasUnknown()) {
        addError(DiagCode::ValueMustNotBeUnknown, range);
        return false;
    }
    return true;
}

bool BindContext::checkPositive(const SVInt& value, SourceRange range) const {
    if (value.isSigned() && value.isNegative()) {
        addError(DiagCode::ValueMustBePositive, range);
        return false;
    }
    return true;
}

optional<bitwidth_t> BindContext::checkValidBitWidth(const SVInt& value, SourceRange range) const {
    auto result = value.as<bitwidth_t>();
    if (!result)
        addError(DiagCode::ValueExceedsMaxBitWidth, range) << (int)SVInt::MAX_BITS;
    return result;
}

BindContext BindContext::resetFlags(bitmask<BindFlags> addedFlags) const {
    // Remove non-sticky flags, add in any extras specified by addedFlags
    BindContext result(*this);
    result.flags &= ~(BindFlags::InsideConcatenation | BindFlags::AllowDataType);
    result.flags |= addedFlags;
    return result;
}

}