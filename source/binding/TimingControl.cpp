//------------------------------------------------------------------------------
// TimingControl.cpp
// Timing control creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/TimingControl.h"

#include "slang/binding/Expressions.h"
#include "slang/compilation/Compilation.h"

namespace slang {

const TimingControl& TimingControl::bind(const TimingControlSyntax& syntax,
                                         const BindContext& context) {
    auto& comp = context.scope.getCompilation();
    TimingControl* result;
    switch (syntax.kind) {
        case SyntaxKind::DelayControl:
            result = &DelayControl::fromSyntax(comp, syntax.as<DelaySyntax>(), context);
            break;
        case SyntaxKind::CycleDelay:
        case SyntaxKind::ImplicitEventControl:
        case SyntaxKind::EventControl:
        case SyntaxKind::EventControlWithExpression:
        case SyntaxKind::RepeatedEventControl:
            context.addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
            result = &badCtrl(comp, nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

TimingControl& TimingControl::badCtrl(Compilation& compilation, const TimingControl* ctrl) {
    return *compilation.emplace<InvalidTimingControl>(ctrl);
}

TimingControl& DelayControl::fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                        const BindContext& context) {
    auto& expr = Expression::bind(*syntax.delayValue, context);
    auto result = compilation.emplace<DelayControl>(expr);
    if (expr.bad())
        return badCtrl(compilation, result);

    if (!expr.type->isNumeric()) {
        context.addDiag(DiagCode::DelayNotNumeric, expr.sourceRange) << *expr.type;
        return badCtrl(compilation, result);
    }

    return *result;
}

} // namespace slang