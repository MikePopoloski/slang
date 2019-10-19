//------------------------------------------------------------------------------
// TimeScaleSymbolBase.h
// Shared timescale helper class.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/Time.h"
#include "slang/text/SourceLocation.h"

namespace slang {

class Scope;
struct ModuleDeclarationSyntax;
struct TimeUnitsDeclarationSyntax;

/// A helper base class for symbols that have an associated time scale.
class TimeScaleSymbolBase {
protected:
    void setTimeScale(const Scope& scope, const TimeUnitsDeclarationSyntax& syntax, bool isFirst);
    void finalizeTimeScale(const Scope& parentScope, const ModuleDeclarationSyntax& syntax);

    TimeScale timeScale;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;
};

} // namespace slang