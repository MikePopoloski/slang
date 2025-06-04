// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
#pragma once

#include "Test.h"
#include "TidyFactory.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"

inline bool runCheckTest(const std::string& checkName, std::string_view code,
                         std::optional<TidyConfig> inputConfig = {},
                         std::string* output = nullptr) {
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
    auto check = Registry::create(checkName);
    auto result = check->check(root, analysisManager);

    if (output) {
        DiagnosticEngine diagEngine(*compilation.getSourceManager());
        diagEngine.setMessage(check->diagCode(), check->diagMessage());
        diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto& diags = check->getDiagnostics();

        auto client = std::make_shared<TextDiagnosticClient>();
        diagEngine.addClient(client);

        for (auto& diag : diags) {
            diagEngine.issue(diag);
        }

        *output = client->getString();
    }

    return result;
}
