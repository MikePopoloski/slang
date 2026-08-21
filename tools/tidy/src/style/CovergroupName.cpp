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

namespace covergroup_name {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const CovergroupDeclarationSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (!boost::regex_match(std::string(node.name.valueText()),
                                config.getCheckConfigs().covergroupRegexPattern)) {
            diags.add(diag::CovergroupName, node.name.location())
                << config.getCheckConfigs().covergroupRegexString;
        }
    }
};
} // namespace covergroup_name

using namespace covergroup_name;

class CovergroupName : public TidyCheck {
public:
    [[maybe_unused]] explicit CovergroupName(TidyKind kind,
                                             std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::CovergroupName; }

    std::string diagString() const override {
        return "name must match supplied covergroup pattern '{}'";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "CovergroupName"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces naming style for covergroups "
               "configured with covergroupRegexString e.g. \"cg_.*\"";
    }
};

REGISTER(CovergroupName, CovergroupName, TidyKind::Style)
