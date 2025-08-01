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

namespace always_ff_assignment_outside_conditional {
struct AlwaysFFVisitor : public ASTVisitor<AlwaysFFVisitor, true, true, false, true> {
    explicit AlwaysFFVisitor(const std::string_view name, const std::string_view resetName) :
        name(name), resetName(resetName) {};

    void handle(const ConditionalStatement& statement) {
        // Early return, if there's no else clause on the conditional statement
        if (!statement.ifFalse) {
            return;
        }

        // Check if there is a reset in the conditional statement
        LookupIdentifier lookupIdentifierVisitor(resetName, false);
        for (const auto& condition : statement.conditions) {
            condition.expr->visit(lookupIdentifierVisitor);

            if (lookupIdentifierVisitor.found()) {
                condStatmenentWithReset = true;
                return;
            }
        }
    }

    void handle(const AssignmentExpression& expression) {
        if (LookupLhsIdentifier::hasIdentifier(name, expression)) {
            assignedOutsideIfReset = true;
            errorLocation = getExpressionSourceLocation(expression);
        }
    }

    bool hasError() { return condStatmenentWithReset && assignedOutsideIfReset; }

    std::optional<SourceLocation> getErrorLocation() const { return errorLocation; }

private:
    const std::string_view name;
    const std::string_view resetName;
    bool condStatmenentWithReset = false;
    bool assignedOutsideIfReset = false;
    std::optional<SourceLocation> errorLocation;
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    const AnalysisManager& analysisManager;

    MainVisitor(Diagnostics& diagnostics, const AnalysisManager& analysisManager) :
        TidyVisitor(diagnostics), analysisManager(analysisManager) {}

    void handle(const VariableSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        auto drivers = analysisManager.getDrivers(symbol);
        if (drivers.empty())
            return;

        auto firstDriver = drivers[0].first;
        if (firstDriver && firstDriver->source == DriverSource::AlwaysFF) {
            AlwaysFFVisitor visitor(symbol.name, config.getCheckConfigs().resetName);
            firstDriver->containingSymbol->visit(visitor);
            if (visitor.hasError()) {
                diags.add(diag::RegisterNotAssignedOnReset,
                          visitor.getErrorLocation().value_or(symbol.location))
                    << symbol.name;
            }
        }
    }
};
} // namespace always_ff_assignment_outside_conditional

using namespace always_ff_assignment_outside_conditional;

class AlwaysFFAssignmentOutsideConditional : public TidyCheck {
public:
    explicit AlwaysFFAssignmentOutsideConditional(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const AnalysisManager& analysisManager) override {
        MainVisitor visitor(diagnostics, analysisManager);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::RegisterNotAssignedOnReset; }

    std::string diagString() const override {
        return "register '{}' has an assignment outside a conditional block with reset. Consider "
               "moving the register to an always_ff that has no reset or moving the assignment "
               "inside the conditional block";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "AlwaysFFAssignmentOutsideConditional"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "A register in an always_ff with an assignment outside a conditional block with a "
               "reset signal on its sensitivity list";
    }
};

REGISTER(AlwaysFFAssignmentOutsideConditional, AlwaysFFAssignmentOutsideConditional,
         TidyKind::Synthesis)
