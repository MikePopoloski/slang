// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace xilinx_do_not_care_values {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const IntegerLiteral& expr) {
        if (auto syntax = expr.syntax; syntax) {
            auto strSyntax = SyntaxPrinter().setIncludeTrivia(false).print(*syntax).str();
            bool hasDoNotCare = strSyntax.find('?') != std::string::npos;
            bool hasDecimal = strSyntax.find('d') != std::string::npos;

            if (hasDoNotCare && hasDecimal)
                diags.add(diag::XilinxDoNotCareValues, syntax->sourceRange());
        }
    }
};
} // namespace xilinx_do_not_care_values

using namespace xilinx_do_not_care_values;

class XilinxDoNotCareValues : public TidyCheck {
public:
    explicit XilinxDoNotCareValues(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::XilinxDoNotCareValues; }

    std::string diagString() const override {
        return "use of x'd? for do-not-care values is not recommended use x'b? instead";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "XilinxDoNotCareValues"; }

    std::string description() const override {
        return "The use of x'd? notation for do-not-care values is not recommended since it has "
               "been observed to produce unexpected results for Xilinx synthesis engines. In "
               "particular for Xilinx synthesis tools, 4'd? is not interpreted as 4'd???? or 4'b?.";
    }

    std::string shortDescription() const override {
        return "The use of x'd? notation for do-not-care values is not recommended since it has "
               "been observed to produce unexpected results for Xilinx synthesis engines.";
    }
};

REGISTER(XilinxDoNotCareValues, XilinxDoNotCareValues, TidyKind::Synthesis)
