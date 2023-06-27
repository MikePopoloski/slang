// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace register_has_no_reset {
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

    const std::string_view name;
    const std::string_view resetName;
    bool correctlyAssignedOnIfReset = false;
    bool assignedOutsideIfReset = false;
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
                diags.add(diag::RegisterNotAssignedOnReset, symbol.location) << symbol.name;
            }
        }
    }
};
} // namespace register_has_no_reset

using namespace register_has_no_reset;

class RegisterHasNoReset : public TidyCheck {
public:
    explicit RegisterHasNoReset(TidyKind kind) : TidyCheck(kind) {}

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

    std::string name() const override { return "RegisterHasNoReset"; }

    std::string description() const override {
        return "A register in an always_ff, which contains the reset signal on its sensitivity "
               "list, which\ndo not have a value when the design is on reset. This will cause "
               "errors with "
               "synthesis\ntools since they will use an incorrect register cell.\n\n" +
               fmt::format(fmt::emphasis::italic,
                           "module m (logic clk, logic reset);\n"
                           "    logic r;\n"
                           "    always_ff @(posedge clk or negedge reset) begin\n"
                           "                               ^^^^^^^^^^^^^------\\\n"
                           "                                                  \\\n"
                           "        r <= 1'b1;                                \\\n"
                           "        ^~~~Register r do not have a value when reset\n"
                           "    end\n"
                           "endmodule\n\n") +
               "Instead the always_ff should be written like this:\n\n" +
               fmt::format(fmt::emphasis::italic, "module m (logic clk, logic reset);\n"
                                                  "    logic r;\n"
                                                  "    always_ff @(posedge clk) begin\n"
                                                  "        r <= 1'b1;\n"
                                                  "    end\n"
                                                  "endmodule\n");
    }

    std::string shortDescription() const override {
        return "A register in an always_ff, which contains the reset signal on its sensitivity "
               "list, which do not have a value when the design is on reset.";
    }
};

REGISTER(RegisterHasNoReset, RegisterHasNoReset, TidyKind::Synthesis)
