// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"
#include "fmt/ranges.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace enforce_port_suffix {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const PortSymbol& port) {
        NEEDS_SKIP_SYMBOL(port)

        const auto& checkConfig = config.getCheckConfigs();
        if (port.isNullPort)
            return;

        if (port.name == checkConfig.clkName || port.name == checkConfig.resetName)
            return;

        std::vector<std::string> const* suffixes;

        if (port.direction == slang::ast::ArgumentDirection::In)
            suffixes = &checkConfig.inputPortSuffix;
        else if (port.direction == slang::ast::ArgumentDirection::Out)
            suffixes = &checkConfig.outputPortSuffix;
        else
            suffixes = &checkConfig.inoutPortSuffix;

        bool matched = suffixes->empty(); // no error is thrown without a suffix
        for (auto& suffix : *suffixes) {
            matched |= port.name.ends_with(suffix);
        }
        if (!matched) {
            auto& diag = diags.add(diag::EnforcePortSuffix, port.location) << port.name;
            if (suffixes->size() == 1) {
                diag << fmt::format("\"{}\"", suffixes->front());
            }
            else {
                diag << fmt::format("{}", *suffixes);
            }
        }
    }
};
} // namespace enforce_port_suffix

using namespace enforce_port_suffix;
class EnforcePortSuffix : public TidyCheck {
public:
    [[maybe_unused]] explicit EnforcePortSuffix(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::EnforcePortSuffix; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "port '{}' is not correctly suffixed with suffix: {}";
    }
    std::string name() const override { return "EnforcePortSuffix"; }
    std::string description() const override {
        return "Enforces that all ports in the design follow the code guidelines provided in the "
               "configuration file by the configs " +
               fmt::format(fmt::emphasis::italic, "inputPortSuffix") + " , " +
               fmt::format(fmt::emphasis::italic, "outputPortSuffix") + " , " +
               fmt::format(fmt::emphasis::italic, "inoutPortSuffix") + '\n';
    }
    std::string shortDescription() const override {
        return "Enforces that all ports in the design follows the code guidelines provided in the "
               "configuration file";
    }
};

REGISTER(EnforcePortSuffix, EnforcePortSuffix, TidyKind::Style)
