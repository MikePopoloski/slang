// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include <algorithm>

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::analysis;

namespace struct_fields_in_same_process {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::StatementsCanonical> {
    const AnalysisManager& analysisManager;

    MainVisitor(Diagnostics& diagnostics, const AnalysisManager& analysisManager) :
        TidyVisitor(diagnostics), analysisManager(analysisManager) {}

    void handle(const VariableSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        checkStructDrivers(symbol);
    }

    void handle(const NetSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        checkStructDrivers(symbol);
    }

private:
    /// Reports structs whose fields are driven from more than one process. Splitting the
    /// fields of a single struct across several processes is a scheduling hazard for tools
    /// that schedule on whole-variable granularity, such as Verilator.
    void checkStructDrivers(const ValueSymbol& symbol) {
        if (!symbol.getType().isStruct())
            return;

        // Drivers are reported in bit order rather than source order, so keep the
        // earliest assignment of each always_comb block as its representative.
        auto isEarlier = [](const ValueDriver* lhs, const ValueDriver* rhs) {
            return lhs->getSourceRange().start() < rhs->getSourceRange().start();
        };

        SmallMap<const Symbol*, const ValueDriver*, 4> combBlocks;
        const ValueDriver* continuousDriver = nullptr;

        for (auto driver : analysisManager.getDrivers(symbol)) {
            // Port connections and declaration initializers are not written by the user
            // as assignments to this symbol, so they can't take part in a race here.
            if (driver->isUnidirectionalPort() || driver->flags.has(DriverFlags::Initializer))
                continue;

            if (driver->kind == DriverKind::Continuous) {
                if (!continuousDriver || isEarlier(driver, continuousDriver))
                    continuousDriver = driver;
            }
            else if (driver->source == DriverSource::AlwaysComb) {
                auto& rep = combBlocks[&*driver->containingSymbol];
                if (!rep || isEarlier(driver, rep))
                    rep = driver;
            }
        }

        // Driving every field continuously is allowed no matter how many assignments are
        // used, so a continuous driver only conflicts if an always_comb drives the struct
        // as well.
        if (combBlocks.empty())
            return;

        std::vector<const ValueDriver*> offenders;
        offenders.reserve(combBlocks.size() + 1);
        for (auto& [block, driver] : combBlocks)
            offenders.push_back(driver);

        if (continuousDriver)
            offenders.push_back(continuousDriver);

        if (offenders.size() < 2)
            return;

        // Report on the last of the conflicting assignments in source order, so that the
        // diagnostic points at an assignment rather than at the declaration.
        auto last = *std::max_element(offenders.begin(), offenders.end(), isEarlier);

        diags.add(diag::StructFieldsInSameProcess, last->getSourceRange()) << symbol.name;
    }
};
} // namespace struct_fields_in_same_process

using namespace struct_fields_in_same_process;

class StructFieldsInSameProcess : public TidyCheck {
public:
    [[maybe_unused]] explicit StructFieldsInSameProcess(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const AnalysisManager& analysisManager) override {
        MainVisitor visitor(diagnostics, analysisManager);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::StructFieldsInSameProcess; }

    std::string diagString() const override {
        return "fields of struct '{}' are driven from more than one process; drive all of them "
               "from the same always_comb or use only continuous assignments";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "StructFieldsInSameProcess"; }

    std::string description() const override {
        return "Splitting the fields of a struct across several always_comb blocks, or mixing "
               "continuous assignments with an always_comb, creates a scheduling race in tools "
               "that schedule on whole-variable granularity, such as Verilator: the struct is "
               "treated as a single object, so each process appears to both read and write it. " +
               shortDescription();
    }

    std::string shortDescription() const override {
        return "Checks that the fields of a struct are all driven from the same always_comb, or "
               "else all driven by continuous assignments.";
    }
};

REGISTER(StructFieldsInSameProcess, StructFieldsInSameProcess, TidyKind::Synthesis)
