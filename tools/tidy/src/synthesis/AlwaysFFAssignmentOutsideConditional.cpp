// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace always_ff_assignment_outside_conditional {
struct AlwaysFFVisitor : public ASTVisitor<AlwaysFFVisitor, true, true> {
    explicit AlwaysFFVisitor(const std::string_view name, const std::string_view resetName) :
        name(name), resetName(resetName){};

    void handle(const ConditionalStatement& statement) {
        // Early return, if there's no else clause on the conditional statement
        if (!statement.ifFalse) {
            return;
        }

        // Collect all the identifiers in the conditions
        CollectIdentifiers collectIdentifiersVisitor;
        for (const auto& condition : statement.conditions) {
            condition.expr->visit(collectIdentifiersVisitor);
        }

        // Check if one of the identifiers is a reset
        const auto isReset =
            std::ranges::any_of(collectIdentifiersVisitor.identifiers, [this](auto id) {
                return id.find(resetName) != std::string_view::npos;
            });

        condStatmenentWithReset = isReset;
    }

    void handle(const AssignmentExpression& expression) {
        if (LookupLhsIdentifier::hasIdentifier(name, expression)) {
            assignedOutsideIfWithReset = true;
            errorLocation = expression.left().syntax->getFirstToken().location();
        }
    }

    bool hasError() { return condStatmenentWithReset && assignedOutsideIfWithReset; }

    const std::string_view name;
    const std::string_view resetName;
    bool condStatmenentWithReset = false;
    bool assignedOutsideIfWithReset = false;
    SourceLocation errorLocation = SourceLocation();
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const VariableSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (symbol.drivers().empty())
            return;

        auto firstDriver = *symbol.drivers().begin();
        if (firstDriver && firstDriver->isInAlwaysFFBlock()) {
            AlwaysFFVisitor visitor(symbol.name, config.getCheckConfigs().resetName);
            firstDriver->containingSymbol->visit(visitor);
            if (visitor.hasError()) {
                diags.add(diag::RegisterNotAssignedOnReset, visitor.errorLocation) << symbol.name;
            }
        }
    }
};
} // namespace always_ff_assignment_outside_conditional

using namespace always_ff_assignment_outside_conditional;

class AlwaysFFAssignmentOutsideConditional : public TidyCheck {
public:
    explicit AlwaysFFAssignmentOutsideConditional(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::RegisterNotAssignedOnReset; }

    std::string diagString() const override {
        return "register '{}' has an assignment outside a conditional block with reset. Consider "
               "moving the register to an always_ff that has no reset or moving the assignment "
               "inside the conditional block";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "AlwaysFFAssignmentOutsideConditional"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "A register in an always_ff with an assignment outside a conditional block with a "
               "reset signal on its sensitivity list";
    }
};

REGISTER(AlwaysFFAssignmentOutsideConditional, AlwaysFFAssignmentOutsideConditional,
         TidyKind::Synthesis)
