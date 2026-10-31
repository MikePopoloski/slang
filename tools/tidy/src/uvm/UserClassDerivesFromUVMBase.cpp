// SPDX-FileCopyrightText: Srinivasan Venkataramanan
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

using namespace slang;
using namespace slang::ast;

namespace user_class_derives_from_uvm_base {

// A class declared directly in uvm_pkg is part of the UVM library. This also covers
// UVM classes without the uvm_ prefix (e.g. get_t) and specializations of generic UVM
// classes, which share the generic class's parent scope.
static bool isUVMLibraryClass(const ClassType& cls) {
    auto scope = cls.getParentScope();
    if (!scope)
        return false;

    auto& sym = scope->asSymbol();
    return sym.kind == SymbolKind::Package && sym.name == "uvm_pkg";
}

static bool lacksUVMBaseClass(const ClassType& cls) {
    for (auto base = cls.getBaseClass(); base;) {
        // An unresolved base is a compile error, not a lint finding.
        if (!base->isClass())
            return false;

        auto& baseClass = base->getCanonicalType().as<ClassType>();
        if (isUVMLibraryClass(baseClass))
            return false;

        base = baseClass.getBaseClass();
    }
    return true;
}

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::StatementsCanonical> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ClassType& cls) {
        NEEDS_SKIP_SYMBOL(cls)

        // Don't check UVM's own classes or descend into them.
        if (isUVMLibraryClass(cls))
            return;

        // An interface class may only extend interface classes, so it can never
        // have a UVM base class; classes implementing it are checked instead.
        if (!cls.isInterface && lacksUVMBaseClass(cls))
            diags.add(diag::UserClassDerivesFromUVMBase, cls.location) << cls.name;
        visitDefault(cls);
    }
};
} // namespace user_class_derives_from_uvm_base

using namespace user_class_derives_from_uvm_base;

class UserClassDerivesFromUVMBase : public TidyCheck {
public:
    [[maybe_unused]] explicit UserClassDerivesFromUVMBase(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::UserClassDerivesFromUVMBase; }

    std::string diagString() const override {
        return "class '{}' does not derive from any UVM base class";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "UserClassDerivesFromUVMBase"; }

    std::string description() const override {
        return "Checks that every class derives from a UVM base class somewhere in its "
               "inheritance chain. Classes declared in uvm_pkg and interface classes are "
               "exempt. Disabled by default.";
    }

    std::string shortDescription() const override {
        return "Checks that every class derives from a UVM base class somewhere in its "
               "inheritance chain.";
    }
};

REGISTER(UserClassDerivesFromUVMBase, UserClassDerivesFromUVMBase, TidyKind::UVM)
