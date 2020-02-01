//------------------------------------------------------------------------------
// TimeScaleSymbolBase.cpp
// Shared timescale helper class
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/TimeScaleSymbolBase.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/parsing/Token.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

void TimeScaleSymbolBase::setTimeScale(const Scope& scope, const TimeUnitsDeclarationSyntax& syntax,
                                       bool isFirst) {
    bool errored = false;
    auto handle = [&](Token token, optional<SourceRange>& prevRange, TimeScaleValue& value) {
        // If there were syntax errors just bail out, diagnostics have already been issued.
        if (token.isMissing() || token.kind != TokenKind::TimeLiteral)
            return;

        auto val = TimeScaleValue::fromLiteral(token.realValue(), token.numericFlags().unit());
        if (!val) {
            scope.addDiag(diag::InvalidTimeScaleSpecifier, token.location());
            return;
        }

        if (prevRange) {
            // If the value was previously set, we need to make sure this new
            // value is exactly the same, otherwise we error.
            if (value != *val && !errored) {
                auto& diag = scope.addDiag(diag::MismatchedTimeScales, token.range());
                diag.addNote(diag::NotePreviousDefinition, prevRange->start()) << *prevRange;
                errored = true;
            }
        }
        else {
            // The first time scale declarations must be the first elements in the parent scope.
            if (!isFirst && !errored) {
                scope.addDiag(diag::TimeScaleFirstInScope, token.range());
                errored = true;
            }

            value = *val;
            prevRange = token.range();
        }
    };

    if (syntax.keyword.kind == TokenKind::TimeUnitKeyword) {
        handle(syntax.time, unitsRange, timeScale.base);
        if (syntax.divider)
            handle(syntax.divider->value, precisionRange, timeScale.precision);
    }
    else {
        handle(syntax.time, precisionRange, timeScale.precision);
    }
}

void TimeScaleSymbolBase::finalizeTimeScale(const Scope& parentScope,
                                            const ModuleDeclarationSyntax& syntax) {
    // If no time unit was set, infer one based on the following rules:
    // - If the scope is nested (inside another definition), inherit from that definition.
    // - Otherwise use a `timescale directive if there is one.
    // - Otherwise, look for a time unit in the compilation scope.
    // - Finally use the compilation default.
    if (unitsRange && precisionRange)
        return;

    optional<TimeScale> ts;
    auto& comp = parentScope.getCompilation();
    if (parentScope.asSymbol().kind == SymbolKind::CompilationUnit)
        ts = comp.getDirectiveTimeScale(syntax);

    if (!ts)
        ts = parentScope.getTimeScale();

    if (!unitsRange)
        timeScale.base = ts->base;
    if (!precisionRange)
        timeScale.precision = ts->precision;
}

} // namespace slang