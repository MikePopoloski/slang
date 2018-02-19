//------------------------------------------------------------------------------
// BindContext.h
// Expression binding context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "symbols/Scope.h"
#include "util/Util.h"

namespace slang {

enum class BindFlags : uint8_t {
    None = 0,
    Constant = 1,
    IntegralConstant = 2,
    InsideConcatenation = 4
};
BITMASK_DEFINE_MAX_ELEMENT(BindFlags, InsideConcatenation);

struct BindContext {
    const Scope& scope;
    LookupNameKind lookupKind = LookupNameKind::Variable;
    LookupLocation lookupLocation;
    bitmask<BindFlags> flags;

    BindContext(const Scope& scope, LookupLocation lookupLocation, bitmask<BindFlags> flags = BindFlags::None) :
        scope(scope), lookupLocation(lookupLocation), flags(flags) {}

    BindContext withFlags(bitmask<BindFlags> addedFlags) const {
        BindContext result(*this);
        result.flags |= addedFlags;
        return result;
    }
};

}