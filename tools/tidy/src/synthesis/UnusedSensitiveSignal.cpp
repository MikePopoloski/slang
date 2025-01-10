// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"
#include <algorithm>
#include <regex>

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace unused_sensitive_signal {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    struct CollectAllIdentifiers
        : public slang::ast::ASTVisitor<CollectAllIdentifiers, true, true> {
        void handle(const slang::ast::NamedValueExpression& expression) {
            if (auto* symbol = expression.getSymbolReference(); symbol && expression.syntax) {
                identifiers.push_back(
                    std::make_pair(symbol->name, getExpressionSourceLocation(expression).value()));
            }
        }
        std::vector<std::pair<std::string_view, SourceLocation>> identifiers;
    };

    void handle(const ProceduralBlockSymbol& block) {
        NEEDS_SKIP_SYMBOL(block)

        if (block.procedureKind != ProceduralBlockKind::AlwaysFF &&
            block.procedureKind != ProceduralBlockKind::Always)
            return;

        if (block.getBody().kind != StatementKind::Timed ||
            block.getBody().as<TimedStatement>().stmt.kind != StatementKind::Block)
            return;

        CollectAllIdentifiers stmtIdVisitor, timingIdVisitor;
        block.getBody().as<TimedStatement>().stmt.as<BlockStatement>().visitStmts(stmtIdVisitor);
        block.getBody().as<TimedStatement>().timing.visit(timingIdVisitor);

        auto compare = [](const auto& a, const auto& b) { return a.first < b.first; };

        std::sort(timingIdVisitor.identifiers.begin(), timingIdVisitor.identifiers.end(), compare);
        std::sort(stmtIdVisitor.identifiers.begin(), stmtIdVisitor.identifiers.end(), compare);

        std::vector<std::pair<std::string_view, SourceLocation>> unusedSignals;

        std::set_difference(timingIdVisitor.identifiers.begin(), timingIdVisitor.identifiers.end(),
                            stmtIdVisitor.identifiers.begin(), stmtIdVisitor.identifiers.end(),
                            std::back_inserter(unusedSignals), compare);

        for (auto signal : unusedSignals) {
            // either match against clkName or against the regex pattern
            if (signal.first != config.getCheckConfigs().clkName &&
                !(std::regex_match(std::string(signal.first),
                                   config.getCheckConfigs().clkNameRegexPattern)))
                diags.add(diag::UnusedSensitiveSignal, signal.second) << signal.first;
        }
    }
};
} // namespace unused_sensitive_signal

using namespace unused_sensitive_signal;

class UnusedSensitiveSignal : public TidyCheck {
public:
    [[maybe_unused]] explicit UnusedSensitiveSignal(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::UnusedSensitiveSignal; }

    std::string diagString() const override {
        return "the signal '{}' is in the sensitivity list of a procedural block but is never "
               "referenced in the statement. Consider using the signal inside the procedural block "
               "or removing it from the sensitivity list";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "UnusedSensitiveSignal"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "A signal inside the sensitivity list is never used in the statement of the "
               "procedural block.";
    }
};

REGISTER(UnusedSensitiveSignal, UnusedSensitiveSignal, TidyKind::Synthesis)
