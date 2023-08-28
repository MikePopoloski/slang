// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace cast_signed_index {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ElementSelectExpression& expr) {
        if (auto& selector = expr.selector();
            selector.kind == slang::ast::ExpressionKind::Conversion && selector.type->isSigned())
            diags.add(diag::CastSignedIndex, selector.sourceRange);
    }
};
} // namespace cast_signed_index

using namespace cast_signed_index;

class CastSignedIndex : public TidyCheck {
public:
    [[maybe_unused]] explicit CastSignedIndex(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::CastSignedIndex; }

    std::string diagString() const override {
        return "casting signed indexes can potentially produce negative indexes. Please remove the "
               "cast or make the index unsigned";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "CastSignedIndex"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "The cast of a signed index can potentially produce negative indexes making some "
               "positions unreachable.";
    }
};

REGISTER(CastSignedIndex, CastSignedIndex, TidyKind::Synthesis)
