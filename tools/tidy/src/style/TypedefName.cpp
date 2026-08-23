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

namespace typedef_name {
struct MainVisitor : public TidyVisitor, SyntaxVisitor<MainVisitor> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    bool specializedCheckTakesPrecedence(SyntaxKind typeKind) const {
        switch (typeKind) {
            case SyntaxKind::EnumType:
                return config.isCheckEnabled(TidyKind::Style, "EnumName");
            case SyntaxKind::StructType:
                return config.isCheckEnabled(TidyKind::Style, "StructName");
            case SyntaxKind::UnionType:
                return config.isCheckEnabled(TidyKind::Style, "UnionName");
            default:
                return false;
        }
    }

    bool specializedCheckTakesPrecedence(ForwardTypeRestriction restriction) const {
        switch (restriction) {
            case ForwardTypeRestriction::Enum:
                return config.isCheckEnabled(TidyKind::Style, "EnumName");
            case ForwardTypeRestriction::Struct:
                return config.isCheckEnabled(TidyKind::Style, "StructName");
            case ForwardTypeRestriction::Union:
                return config.isCheckEnabled(TidyKind::Style, "UnionName");
            default:
                return false;
        }
    }

    void checkName(const parsing::Token& name) {
        if (!boost::regex_match(std::string(name.valueText()),
                                config.getCheckConfigs().typedefRegexPattern)) {
            diags.add(diag::TypedefName, name.location())
                << config.getCheckConfigs().typedefRegexString;
        }
    }

    void handle(const TypedefDeclarationSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (specializedCheckTakesPrecedence(node.type->kind))
            return;

        checkName(node.name);
    }

    void handle(const ForwardTypedefDeclarationSyntax& node) {
        NEEDS_SKIP_NODE(node)

        if (node.typeRestriction && specializedCheckTakesPrecedence(
                                        SemanticFacts::getTypeRestriction(*node.typeRestriction)))
            return;

        checkName(node.name);
    }
};
} // namespace typedef_name

using namespace typedef_name;

class TypedefName : public TidyCheck {
public:
    [[maybe_unused]] explicit TypedefName(TidyKind kind,
                                          std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        for (auto& tree : root.getCompilation().getSyntaxTrees())
            tree->root().visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::TypedefName; }

    std::string diagString() const override {
        return "typedef name must match supplied pattern '{}'";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "TypedefName"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Enforces naming style for typedefs "
               "configured with typedefRegexString e.g. \"[a-z_0-9]+_t\". "
               "EnumName, StructName, and UnionName take precedence when enabled.";
    }
};

REGISTER(TypedefName, TypedefName, TidyKind::Style)
