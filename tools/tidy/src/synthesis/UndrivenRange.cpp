// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/ranges.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace undriven_range {
struct UndrivenRangeVisitor : public TidyVisitor, ASTVisitor<UndrivenRangeVisitor, true, true> {
    explicit UndrivenRangeVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    /// Given a set of constant ranges, format them into a string to display in
    /// a diagnostic.
    static auto formatRanges(std::vector<ConstantRange> const& ranges) {
        std::vector<std::string> result;
        for (auto& range : ranges) {
            if (range.lower() == range.upper()) {
                result.push_back(fmt::format("{}", range.lower()));
            }
            else {
                result.push_back(fmt::format("{}:{}", range.lower(), range.upper()));
            }
        }
        return fmt::format("{}", fmt::join(result, ", "));
    }

    void handle(const VariableSymbol& symbol) {

        // If the variable has a fixed range, then determine if any ranges are
        // undriven.
        if (symbol.getType().hasFixedRange()) {
            auto range = symbol.getType().getFixedRange();

            int start = range.lower();
            int end = range.upper();
            int current = start;

            std::vector<ConstantRange> undriven;

            for (auto it = symbol.drivers().begin(); it != symbol.drivers().end(); ++it) {
                auto intervalBounds = it.bounds();

                if (intervalBounds.first > current) {
                    undriven.push_back({current, (int)intervalBounds.first - 1});
                }

                current = std::max(current, (int)intervalBounds.second + 1);
            }

            if (current <= end) {
                undriven.push_back({current, end});
            }

            if (!undriven.empty()) {
                // Issue a diagnostic for any undriven ranges.
                diags.add(diag::UndrivenRange, symbol.location)
                    << symbol.name << formatRanges(undriven);
            }
        }
    }
};
} // namespace undriven_range

using namespace undriven_range;

class UndrivenRange : public TidyCheck {
public:
    [[maybe_unused]] explicit UndrivenRange(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        UndrivenRangeVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::UndrivenRange; }

    std::string diagString() const override { return "variable {} has undriven bits: {}"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "UndrivenRange"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "One or more bits of a variable are undriven and can be a source of Xs in the "
               "design.";
    }
};

REGISTER(UndrivenRange, UndrivenRange, TidyKind::Synthesis)
