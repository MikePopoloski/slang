//------------------------------------------------------------------------------
//! @file OnlyAssignedOnReset.h
//! @brief Only assigned on reset slang-tidy check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace only_assigned_on_reset {
struct AlwaysFFVisitor : public ASTVisitor<AlwaysFFVisitor, true, true> {
    explicit AlwaysFFVisitor(const string_view name, const string_view resetName) :
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
        const auto isReset = std::any_of(collectIdentifiersVisitor.identifiers.begin(),
                                         collectIdentifiersVisitor.identifiers.end(),
                                         [this](auto id) {
                                             return id.find(resetName) != std::string_view::npos;
                                         });

        if (isReset) {
            LookupLhsIdentifier visitor(name);
            statement.ifTrue.visit(visitor);
            if (visitor.found()) {
                visitor.reset();
                statement.ifFalse->visit(visitor);
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

struct MainVisitor : public ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics, const Registry::RegistryCheckConfig& config) :
        diags(diagnostics), config(config) {}

    Diagnostics& diags;
    const Registry::RegistryCheckConfig& config;

    void handle(const VariableSymbol& symbol) {
        if (symbol.drivers().empty())
            return;

        auto firstDriver = *symbol.drivers().begin();
        if (firstDriver && firstDriver->isInAlwaysFFBlock()) {
            AlwaysFFVisitor visitor(symbol.name, config.resetName);
            firstDriver->containingSymbol->visit(visitor);
            if (visitor.hasError()) {
                diags.add(diag::OnlyAssignedOnReset, symbol.location) << symbol.name;
            }
        }
    }
};
} // namespace only_assigned_on_reset

using namespace only_assigned_on_reset;
class OnlyAssignedOnReset : public TidyCheck {
public:
    explicit OnlyAssignedOnReset(const Registry::RegistryCheckConfig& config, TidyKind kind) :
        TidyCheck(config, kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics, config);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::OnlyAssignedOnReset; }

    std::string diagString() const override { return "register '{}' is only assigned on reset"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string_view name() const override { return "OnlyAssignedOnReset"; }

    std::string description() const override {
        return "A register in an always_ff only have value while the design is on reset.\n\n" +
               fmt::format(fmt::emphasis::italic,
                           "module m (logic clk, logic reset);\n"
                           "    logic r;\n"
                           "    always_ff @(posedge clk or negedge reset) begin\n"
                           "        if (~reset) begin\n"
                           "            r <= 1'b0;\n"
                           "        end\n"
                           "        begin\n"
                           "            ~~r do not have a value when design is not in reset\n"
                           "        end\n"
                           "    end\n"
                           "endmodule\n");
    }

    string_view shortDescription() const override {
        return "A register in an always_ff only have value while the design is on reset."sv;
    }
};

REGISTER(OnlyAssignedOnReset, OnlyAssignedOnReset, TidyKind::Synthesis)
