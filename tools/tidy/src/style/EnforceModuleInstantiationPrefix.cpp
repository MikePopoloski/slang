// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace enforce_module_instantiation_prefix {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceSymbol& instance) {
        NEEDS_SKIP_SYMBOL(instance)

        if (!instance.isModule())
            return;

        std::string_view prefix = config.getCheckConfigs().moduleInstantiationPrefix;
        for (auto& member : instance.body.members()) {
            if (member.kind == SymbolKind::Instance && !member.name.starts_with(prefix)) {
                diags.add(diag::EnforceModuleInstantiationPrefix, member.location)
                    << member.name << prefix;
            }
        }
    }
};
} // namespace enforce_module_instantiation_prefix

using namespace enforce_module_instantiation_prefix;
class EnforceModuleInstantiationPrefix : public TidyCheck {
public:
    [[maybe_unused]] explicit EnforceModuleInstantiationPrefix(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::EnforceModuleInstantiationPrefix; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
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
