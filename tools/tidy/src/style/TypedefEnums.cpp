// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace typedef_enums {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const EnumTypeSyntax& node) {
        NEEDS_SKIP_NODE(node)

        auto parent = node.parent;
        if (!parent)
            return;

        if (parent->kind != SyntaxKind::TypedefDeclaration) {
            diags.add(diag::TypedefEnums, node.keyword.location());
        }
    }
};
} // namespace typedef_enums

using namespace typedef_enums;

class TypedefEnums : public TidyCheck {
public:
    [[maybe_unused]] explicit TypedefEnums(TidyKind kind,
                                           std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::TypedefEnums; }

    std::string diagString() const override {
        return "enum declaration should be named using a typedef";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "TypedefEnums"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks that all enum declarations are named using a typedef.";
    }
};

REGISTER(TypedefEnums, TypedefEnums, TidyKind::Style)
