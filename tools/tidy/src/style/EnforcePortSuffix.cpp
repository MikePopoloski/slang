//------------------------------------------------------------------------------
//! @file EnforcePortSuffix.h
//! @brief Enforce port suffix slang-tidy check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace enforce_port_suffix {
struct MainVisitor : public ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics, const TidyConfig::CheckConfigs& config) :
        diags(diagnostics), config(config) {}

    void handle(const PortSymbol& port) {
        if (port.isNullPort)
            return;

        auto symbol = port.internalSymbol;

        if (symbol->name == config.clkName || symbol->name == config.resetName)
            return;

        // TODO: Change this to std::basic_char<>::ends_with one we have c++20
        auto ends_with = [](std::string_view name, std::string_view suffix) {
            return name.size() >= suffix.size() &&
                   !name.compare(name.size() - suffix.size(), suffix.size(), suffix);
        };

        std::string_view suffix;

        if (port.direction == slang::ast::ArgumentDirection::In)
            suffix = config.inputPortSuffix;
        else if (port.direction == slang::ast::ArgumentDirection::Out)
            suffix = config.outputPortSuffix;
        else
            suffix = config.inoutPortSuffix;

        if (!ends_with(symbol->name, suffix)) {
            diags.add(diag::EnforcePortSuffix, port.location) << symbol->name << suffix;
        }
    }

    Diagnostics& diags;
    const TidyConfig::CheckConfigs& config;
};
} // namespace enforce_port_suffix

using namespace enforce_port_suffix;
class EnforcePortSuffix : public TidyCheck {
public:
    [[maybe_unused]] explicit EnforcePortSuffix(const TidyConfig::CheckConfigs& config,
                                                TidyKind kind) :
        TidyCheck(config, kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics, config);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::EnforcePortSuffix; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "port '{}' is not correctly suffixed with suffix: '{}'";
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
