// SPDX-FileCopyrightText: Jonathan Drolet
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"
#include "fmt/ranges.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace enforce_port_prefix {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const PortSymbol& port) {
        NEEDS_SKIP_SYMBOL(port)

        const auto& checkConfig = config.getCheckConfigs();
        if (port.isNullPort)
            return;

        if (port.name == checkConfig.clkName || port.name == checkConfig.resetName)
            return;

        std::vector<std::string> const* prefixes;

        if (port.direction == slang::ast::ArgumentDirection::In)
            prefixes = &checkConfig.inputPortPrefix;
        else if (port.direction == slang::ast::ArgumentDirection::Out)
            prefixes = &checkConfig.outputPortPrefix;
        else
            prefixes = &checkConfig.inoutPortPrefix;

        bool matched = prefixes->empty(); // no error is thrown without a prefix
        for (auto& prefix : *prefixes) {
            matched |= port.name.starts_with(prefix);
        }
        if (!matched) {
            auto& diag = diags.add(diag::EnforcePortPrefix, port.location) << port.name;
            if (prefixes->size() == 1) {
                diag << fmt::format("\"{}\"", prefixes->front());
            }
            else {
                diag << fmt::format("{}", *prefixes);
            }
        }
    }
};
} // namespace enforce_port_prefix

using namespace enforce_port_prefix;
class EnforcePortPrefix : public TidyCheck {
public:
    [[maybe_unused]] explicit EnforcePortPrefix(TidyKind kind,
                                                std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::EnforcePortPrefix; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "port '{}' is not correctly prefixed with prefix: {}";
    }
    std::string name() const override { return "EnforcePortPrefix"; }
    std::string description() const override {
        return "Enforces that all ports in the design follow the code guidelines provided in the "
               "configuration file by the configs " +
               fmt::format(fmt::emphasis::italic, "inputPortPrefix") + " , " +
               fmt::format(fmt::emphasis::italic, "outputPortPrefix") + " , " +
               fmt::format(fmt::emphasis::italic, "inoutPortPrefix") + '\n';
    }
    std::string shortDescription() const override {
        return "Enforces that all ports in the design follows the code guidelines provided in the "
               "configuration file";
    }
};

REGISTER(EnforcePortPrefix, EnforcePortPrefix, TidyKind::Style)
