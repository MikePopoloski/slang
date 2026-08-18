// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include <boost_regex.hpp>

#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace cross_name {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const CoverCrossSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (!node.label) {
            diags.add(diag::CrossName, node.cross.location())
                << "cross must be named and the name must match the pattern"sv
                << config.getCheckConfigs().crossRegexString;
            return;
        }

        if (!boost::regex_match(std::string(node.label->name.valueText()),
                                config.getCheckConfigs().crossRegexPattern)) {
            diags.add(diag::CrossName, node.label->name.location())
                << "name must match supplied cross pattern"sv
                << config.getCheckConfigs().crossRegexString;
        }
    }
};
} // namespace cross_name

using namespace cross_name;

class CrossName : public TidyCheck {
public:
    [[maybe_unused]] explicit CrossName(TidyKind kind,
                                        std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::CrossName; }

    std::string diagString() const override { return "'{}' '{}'"; }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "CrossName"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces naming style for crosss "
               "configured with crossRegexString e.g. \"cg_.*\"";
    }
};

REGISTER(CrossName, CrossName, TidyKind::Style)
