// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
#pragma once

#include "Test.h"
#include "TidyFactory.h"

#include "slang/analysis/AnalysisManager.h"

inline bool runCheckTest(const std::string& checkName, std::string_view code,
                         std::optional<TidyConfig> inputConfig = {}) {
    auto tree = SyntaxTree::fromText(code);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    compilation.freeze();

    analysis::AnalysisManager analysisManager;
    analysisManager.analyze(compilation);

    TidyConfig config;
    Registry::setConfig(inputConfig ? *inputConfig : config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create(checkName);
    return visitor->check(root, analysisManager);
}
