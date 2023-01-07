//------------------------------------------------------------------------------
//! @file RegisterHasNoReset.h
//! @brief Register has no reset slang-tidy check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ASTHelperVisitors.h"
#include "TidyFactory.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace register_has_no_reset {
struct AlwaysFFVisitor : public ASTVisitor<AlwaysFFVisitor, true, true> {
    explicit AlwaysFFVisitor(std::string_view name) : name(name){};

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
        const auto isReset = std::any_of(collectIdentifiersVisitor.identifiers.begin(),
                                         collectIdentifiersVisitor.identifiers.end(), [](auto id) {
                                             return id.find("reset") != std::string_view::npos ||
                                                    id.find("rst") != std::string_view::npos;
                                         });

        if (isReset) {
            LookupLhsIdentifier visitor(name);
            statement.ifFalse->visit(visitor);
            if (visitor.found()) {
                visitor.reset();
                statement.ifTrue.visit(visitor);
                if (!visitor.found()) {
                    correctlyAssignedOnIfReset = true;
                }
            }
        }
    }

    void handle(const AssignmentExpression& expression) {
        if (LookupLhsIdentifier::hasIdentifier(name, expression)) {
            assignedOutsideIfReset = true;
        }
    }

    bool hasError() { return correctlyAssignedOnIfReset && !assignedOutsideIfReset; }

    std::string_view name;
    bool correctlyAssignedOnIfReset = false;
    bool assignedOutsideIfReset = false;
};

struct MainVisitor : public ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : diags(diagnostics) {}
    Diagnostics& diags;

    void handle(const VariableSymbol& symbol) {
        if (symbol.drivers().empty())
            return;

        auto firstDriver = *symbol.drivers().begin();
        if (firstDriver && firstDriver->isInAlwaysFFBlock()) {
            AlwaysFFVisitor visitor(symbol.name);
            firstDriver->containingSymbol->visit(visitor);
            if (visitor.hasError()) {
                diags.add(diag::RegisterNotAssignedOnReset, symbol.location) << symbol.name;
            }
        }
    }
};
} // namespace register_has_no_reset

using namespace register_has_no_reset;
class RegisterHasNoReset : public TidyCheck {
public:
    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::RegisterNotAssignedOnReset; }

    std::string diagString() const override {
        return "register '{}' has no value on reset, but the always_ff block has the reset signal "
               "on the sensitivity list. Consider moving the register to an always_ff that has no "
               "reset or set a value on reset";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string_view name() const override { return "RegisterHasNoReset"; }
};

REGISTER(RegisterHasNoReset, RegisterHasNoReset)
