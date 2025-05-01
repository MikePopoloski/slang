//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/ClockInference.h"
#include "slang/analysis/DataFlowAnalysis.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/text/FormatBuffer.h"

namespace slang::analysis {

using namespace ast;

static void stringifyLSP(const Expression& expr, EvalContext& evalContext, FormatBuffer& buffer) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            buffer.append(expr.as<ValueExpressionBase>().symbol.name);
            break;
        case ExpressionKind::Conversion:
            stringifyLSP(expr.as<ConversionExpression>().operand(), evalContext, buffer);
            break;
        case ExpressionKind::ElementSelect: {
            auto& select = expr.as<ElementSelectExpression>();
            stringifyLSP(select.value(), evalContext, buffer);
            buffer.format("[{}]", select.selector().eval(evalContext).toString());
            break;
        }
        case ExpressionKind::RangeSelect: {
            auto& select = expr.as<RangeSelectExpression>();
            stringifyLSP(select.value(), evalContext, buffer);
            buffer.format("[{}:{}]", select.left().eval(evalContext).toString(),
                          select.right().eval(evalContext).toString());
            break;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            stringifyLSP(access.value(), evalContext, buffer);
            buffer.append(".");
            buffer.append(access.member.name);
            break;
        }
        default:
            SLANG_UNREACHABLE;
    }
}

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {

    DataFlowAnalysis dfa(context, analyzedSymbol, true);
    switch (analyzedSymbol.kind) {
        case SymbolKind::ProceduralBlock:
            dfa.run(analyzedSymbol.as<ProceduralBlockSymbol>().getBody());
            break;
        case SymbolKind::Subroutine:
            dfa.run(analyzedSymbol.as<SubroutineSymbol>().getBody());
            break;
        default:
            SLANG_UNREACHABLE;
    }

    if (dfa.bad)
        return;

    if (parentProcedure || !dfa.getAssertions().empty() || !dfa.getSampledValueCalls().empty()) {
        // All flavors of always and initial blocks can infer a clock.
        if (analyzedSymbol.kind == SymbolKind::ProceduralBlock &&
            analyzedSymbol.as<ProceduralBlockSymbol>().procedureKind !=
                ProceduralBlockKind::Final) {
            inferredClock = dfa.inferClock(parentProcedure);
        }

        // If no procedural inferred clock, check the scope for a default clocking block.
        if (!inferredClock) {
            auto scope = analyzedSymbol.getParentScope();
            SLANG_ASSERT(scope);

            if (auto defaultClocking = scope->getCompilation().getDefaultClocking(*scope))
                inferredClock = &defaultClocking->as<ClockingBlockSymbol>().getEvent();
        }

        if (inferredClock && inferredClock->bad())
            return;

        for (auto& var : dfa.getAssertions()) {
            if (auto stmtPtr = std::get_if<const Statement*>(&var)) {
                auto& stmt = **stmtPtr;
                if (stmt.kind == StatementKind::ProceduralChecker) {
                    for (auto inst : stmt.as<ProceduralCheckerStatement>().instances)
                        assertions.emplace_back(context, inferredClock, *this, stmt, inst);
                }
                else {
                    assertions.emplace_back(context, inferredClock, *this, stmt, nullptr);
                }
            }
            else {
                auto& expr = *std::get<const Expression*>(var);
                assertions.emplace_back(context, inferredClock, this, analyzedSymbol, expr);
            }
        }

        // If we have no inferred clock then all sampled value system calls must provide
        // a clocking argument explicitly.
        if (!inferredClock) {
            for (auto call : dfa.getSampledValueCalls())
                ClockInference::checkSampledValueFuncs(context, analyzedSymbol, *call);
        }
    }

    if (analyzedSymbol.kind == SymbolKind::ProceduralBlock) {
        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();
        if (procedure.procedureKind == ProceduralBlockKind::AlwaysComb) {
            dfa.visitLatches([&](const Symbol&, const Expression& expr) {
                FormatBuffer buffer;
                stringifyLSP(expr, dfa.getEvalContext(), buffer);

                context.addDiag(procedure, diag::InferredLatch, expr.sourceRange) << buffer.str();
            });
        }
    }
    else if (analyzedSymbol.kind == SymbolKind::Subroutine) {
        // Diagnose missing return statements and/or incomplete
        // assignments to the return value var.
        auto& subroutine = analyzedSymbol.as<SubroutineSymbol>();
        if (dfa.isReachable() && subroutine.subroutineKind == SubroutineKind::Function &&
            !subroutine.getReturnType().isVoid() && !subroutine.name.empty()) {

            // Control falls off the end of a non-void function but that is
            // fine if the return value var is definitely assigned here.
            SLANG_ASSERT(subroutine.returnValVar);
            if (!dfa.isDefinitelyAssigned(*subroutine.returnValVar)) {
                if (dfa.hasReturnStatements() || dfa.isReferenced(*subroutine.returnValVar)) {
                    context.addDiag(subroutine, diag::IncompleteReturn, subroutine.location)
                        << subroutine.name;
                }
                else {
                    context.addDiag(subroutine, diag::MissingReturn, subroutine.location)
                        << subroutine.name;
                }
            }
        }
    }
}

} // namespace slang::analysis
