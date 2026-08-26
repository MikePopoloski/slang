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

namespace struct_name {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void checkName(const parsing::Token& name) {
        if (!boost::regex_match(std::string(name.valueText()),
                                config.getCheckConfigs().structRegexPattern)) {
            diags.add(diag::StructName, name.location())
                << config.getCheckConfigs().structRegexString;
        }
    }

    void handle(const TypedefDeclarationSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (node.type->kind != SyntaxKind::StructType)
            return;

        checkName(node.name);
    }

    void handle(const ForwardTypedefDeclarationSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (node.typeRestriction && SemanticFacts::getTypeRestriction(*node.typeRestriction) ==
                                        ForwardTypeRestriction::Struct) {
            checkName(node.name);
        }
    }
};
} // namespace struct_name

using namespace struct_name;

class StructName : public TidyCheck {
public:
    [[maybe_unused]] explicit StructName(TidyKind kind,
                                         std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::StructName; }

    std::string diagString() const override {
        return "struct type name must match supplied pattern '{}'";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "StructName"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces naming style for struct types "
               "configured with structRegexString e.g. \"[a-z_0-9]+_t\"";
    }
};

REGISTER(StructName, StructName, TidyKind::Style)
