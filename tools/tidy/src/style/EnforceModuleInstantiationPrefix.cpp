// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace enforce_module_instantiation_prefix {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::StatementsCanonical> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceSymbol& instance) {
        std::string_view name = instance.name.empty() ? instance.getArrayName() : instance.name;
        std::string_view prefix = config.getCheckConfigs().moduleInstantiationPrefix;
        if (instance.isModule() && !name.empty() && !instance.isTopLevel() &&
            !skip(sourceManager->getFileName((instance).location)) && !name.starts_with(prefix))
            diags.add(diag::EnforceModuleInstantiationPrefix, instance.location) << name << prefix;

        visitDefault(instance);
    }
};
} // namespace enforce_module_instantiation_prefix

using namespace enforce_module_instantiation_prefix;
class EnforceModuleInstantiationPrefix : public TidyCheck {
public:
    [[maybe_unused]] explicit EnforceModuleInstantiationPrefix(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::EnforceModuleInstantiationPrefix; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "module instantiation '{}' is not correctly prefixed with prefix: '{}'";
    }
    std::string name() const override { return "EnforceModuleInstantiationPrefix"; }
    std::string description() const override {
        return "Enforces that module instantiations in the design follows the code guidelines "
               "provided in the configuration file by the config " +
               fmt::format(fmt::emphasis::italic, "moduleInstantiationPrefix");
    }
    std::string shortDescription() const override {
        return "Enforces that module instantiations in the design follows the code guidelines "
               "provided in the configuration file";
    }
};

REGISTER(EnforceModuleInstantiationPrefix, EnforceModuleInstantiationPrefix, TidyKind::Style)
