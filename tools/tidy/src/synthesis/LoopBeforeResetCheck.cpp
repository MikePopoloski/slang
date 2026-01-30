// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::analysis;

namespace loop_before_reset_check {
struct AlwaysFFVisitor : public ASTVisitor<AlwaysFFVisitor, true, true, false, true> {
    explicit AlwaysFFVisitor(const std::string_view resetName, const bool resetIsActiveHigh) :
        resetName(resetName), resetIsActiveHigh(resetIsActiveHigh) {};

    void handle(const ForLoopStatement& statement) {
        // We found a for loop - check if it's at the top level (before reset check)
        if (!insideResetConditional) {
            // Check if this loop contains a reset check inside it
            ResetInLoopVisitor resetVisitor(resetName);
            statement.body.visit(resetVisitor);
            
            if (resetVisitor.hasResetCheck()) {
                hasError = true;
                errorLocation = statement.sourceRange.start();
            }
        }
    }

    void handle(const ConditionalStatement& statement) {
        // Check if there is a reset in the conditional statement
        bool isReset = false;
        bool isResetNeg = false;

        LookupIdentifier lookupIdentifierVisitor(resetName, false);
        for (const auto& condition : statement.conditions) {
            condition.expr->visit(lookupIdentifierVisitor);
            isReset = lookupIdentifierVisitor.found();

            if (isReset) {
                if (condition.expr->kind == ExpressionKind::UnaryOp) {
                    auto op = condition.expr->as<UnaryExpression>().op;
                    isResetNeg = (op == UnaryOperator::BitwiseNot) ||
                                 (op == UnaryOperator::LogicalNot);
                }
                break;
            }
        }

        if (!isReset)
            return;

        // Mark that we're now inside the reset conditional
        bool wasInsideResetConditional = insideResetConditional;
        insideResetConditional = true;

        // Continue visiting the body of the conditional
        if (statement.ifFalse) {
            statement.ifTrue.visit(*this);
            statement.ifFalse->visit(*this);
        }

        // Restore previous state
        insideResetConditional = wasInsideResetConditional;
    }

    bool getHasError() const { return hasError; }

    std::optional<SourceLocation> getErrorLocation() const { return errorLocation; }

private:
    // Helper visitor to check if a loop body contains a reset check
    struct ResetInLoopVisitor : public ASTVisitor<ResetInLoopVisitor, true, true, false, true> {
        explicit ResetInLoopVisitor(const std::string_view resetName) : resetName(resetName) {}

        void handle(const ConditionalStatement& statement) {
            // Check if this conditional statement uses the reset signal
            LookupIdentifier lookupIdentifierVisitor(resetName, false);
            for (const auto& condition : statement.conditions) {
                condition.expr->visit(lookupIdentifierVisitor);
                if (lookupIdentifierVisitor.found()) {
                    foundReset = true;
                    return;
                }
            }
        }

        bool hasResetCheck() const { return foundReset; }

    private:
        const std::string_view resetName;
        bool foundReset = false;
    };

    const std::string_view resetName;
    const bool resetIsActiveHigh;
    bool insideResetConditional = false;
    bool hasError = false;
    std::optional<SourceLocation> errorLocation;
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    const AnalysisManager& analysisManager;

    MainVisitor(Diagnostics& diagnostics, const AnalysisManager& analysisManager) :
        TidyVisitor(diagnostics), analysisManager(analysisManager) {}

    void handle(const ProceduralBlockSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        // Only check always_ff blocks
        if (symbol.procedureKind != ProceduralBlockKind::AlwaysFF)
            return;

        // Check if the body is a timed statement (has sensitivity list)
        if (symbol.getBody().kind != StatementKind::Timed)
            return;

        auto& timedStmt = symbol.getBody().as<TimedStatement>();
        
        // Check if reset signal is present in the sensitivity list
        auto& configs = config.getCheckConfigs();
        LookupIdentifier resetInSensitivityList(configs.resetName, false);
        timedStmt.timing.visit(resetInSensitivityList);
        
        // Only apply the check if reset is in the sensitivity list
        if (!resetInSensitivityList.found())
            return;

        AlwaysFFVisitor visitor(configs.resetName, configs.resetIsActiveHigh);
        symbol.getBody().visit(visitor);
        
        if (visitor.getHasError()) {
            diags.add(diag::LoopBeforeResetCheck,
                      visitor.getErrorLocation().value_or(symbol.location));
        }
    }
};
} // namespace loop_before_reset_check

using namespace loop_before_reset_check;

class LoopBeforeResetCheck : public TidyCheck {
public:
    explicit LoopBeforeResetCheck(TidyKind kind,
                                  std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const AnalysisManager& analysisManager) override {
        MainVisitor visitor(diagnostics, analysisManager);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::LoopBeforeResetCheck; }

    std::string diagString() const override {
        return "loop statement contains reset check inside the loop body. For synthesis "
               "compatibility, the reset check should be the outermost conditional, with the "
               "loop nested inside both the reset and non-reset branches";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "LoopBeforeResetCheck"; }

    std::string description() const override {
        return "Checks for loop statements (e.g., for loops) that contain a reset check inside "
               "the loop body in always_ff blocks. This pattern is not synthesizable by most "
               "synthesis tools (e.g., Design Compiler) because they expect the reset check to "
               "be the outermost conditional statement.\n\n" +
               fmt::format(fmt::emphasis::italic,
                           "// BAD: Loop before reset check (not synthesizable)\n"
                           "always_ff @(posedge clk_i or negedge rst_ni) begin\n"
                           "    for (int unsigned i = 0; i < QUEUE_ENTRIES; ++i) begin\n"
                           "        if (~rst_ni) begin\n"
                           "            flop[i] <= '0;\n"
                           "        end else begin\n"
                           "            flop[i] <= a[i];\n"
                           "        end\n"
                           "    end\n"
                           "end\n\n") +
               "Instead, the reset check should be outermost:\n\n" +
               fmt::format(fmt::emphasis::italic,
                           "// GOOD: Reset check before loop (synthesizable)\n"
                           "always_ff @(posedge clk_i or negedge rst_ni) begin\n"
                           "    if (~rst_ni) begin\n"
                           "        for (int unsigned i = 0; i < QUEUE_ENTRIES; ++i) begin\n"
                           "            flop[i] <= '0;\n"
                           "        end\n"
                           "    end else begin\n"
                           "        for (int unsigned i = 0; i < QUEUE_ENTRIES; ++i) begin\n"
                           "            flop[i] <= a[i];\n"
                           "        end\n"
                           "    end\n"
                           "end\n");
    }

    std::string shortDescription() const override {
        return "Loop statement contains reset check inside the loop body, which is not "
               "synthesizable by most tools";
    }
};

REGISTER(LoopBeforeResetCheck, LoopBeforeResetCheck, TidyKind::Synthesis)
