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

namespace coverpoint_name {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const CoverpointSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (!node.label) {
            diags.add(diag::CoverpointName, node.coverpoint.location())
                << "coverpoint must be named and the name must match the pattern"sv
                << config.getCheckConfigs().coverpointRegexString;
            return;
        }

        if (!boost::regex_match(std::string(node.label->name.valueText()),
                                config.getCheckConfigs().coverpointRegexPattern)) {
            diags.add(diag::CoverpointName, node.label->name.location())
                << "name must match supplied coverpoint pattern"sv
                << config.getCheckConfigs().coverpointRegexString;
        }
    }
};
} // namespace coverpoint_name

using namespace coverpoint_name;

class CoverpointName : public TidyCheck {
public:
    [[maybe_unused]] explicit CoverpointName(TidyKind kind,
                                             std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::CoverpointName; }

    std::string diagString() const override { return "'{}' '{}'"; }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "CoverpointName"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces naming style for coverpoints "
               "configured with coverpointRegexString e.g. \"cg_.*\"";
    }
};

REGISTER(CoverpointName, CoverpointName, TidyKind::Style)
