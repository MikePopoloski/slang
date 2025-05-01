// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
#pragma once

#include "Test.h"
#include <fmt/format.h>

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisManager.h"

#define CHECK_DIAGS_EMPTY              \
    do {                               \
        if (!diags.empty()) {          \
            FAIL_CHECK(report(diags)); \
        }                              \
    } while (0)

using namespace slang::analysis;

inline std::pair<Diagnostics, AnalyzedDesign> analyze(const std::string& text,
                                                      Compilation& compilation,
                                                      AnalysisManager& analysisManager) {
    auto tree = SyntaxTree::fromText(text);
    compilation.addSyntaxTree(tree);
    auto diags = compilation.getAllDiagnostics();
    if (!std::ranges::all_of(diags, [](auto& diag) { return !diag.isError(); })) {
        FAIL_CHECK(report(diags));
        return {};
    }

    compilation.freeze();

    auto design = analysisManager.analyze(compilation);
    return {analysisManager.getDiagnostics(compilation.getSourceManager()), design};
}
