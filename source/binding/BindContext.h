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
    RequireConstant = 1
};
BITMASK_DEFINE_MAX_ELEMENT(BindFlags, RequireConstant);

struct BindContext {
    const Scope& scope;
    LookupNameKind lookupKind = LookupNameKind::Variable;
    LookupLocation lookupLocation;
    BindFlags flags;

    BindContext(const Scope& scope, LookupLocation lookupLocation, BindFlags flags = BindFlags::None) :
        scope(scope), lookupLocation(lookupLocation), flags(flags) {}
};

}