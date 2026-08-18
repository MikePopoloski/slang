// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace typedef_struct_union {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const StructUnionTypeSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (auto parent = node.parent) {
            bool isTypedef = parent->kind == SyntaxKind::TypedefDeclaration;
            bool allowedNestedAnon = config.getCheckConfigs().allowNestedAnon &&
                                     parent->kind == SyntaxKind::StructUnionMember;
            if (!isTypedef && !allowedNestedAnon) {
                diags.add(diag::TypedefStructUnion, node.keyword.location());
            }
        }

        visitDefault(node);
    }
};
} // namespace typedef_struct_union

using namespace typedef_struct_union;

class TypedefStructUnion : public TidyCheck {
public:
    [[maybe_unused]] explicit TypedefStructUnion(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::TypedefStructUnion; }

    std::string diagString() const override {
        return "struct/union declaration should be named using a typedef";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "TypedefStructUnion"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces that all struct and union declarations are named using a typedef "
               "unless allowNestedAnon is set in the config";
    }
};

REGISTER(TypedefStructUnion, TypedefStructUnion, TidyKind::Style)
