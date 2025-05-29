// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"

auto reportDiagnostics(std::unique_ptr<TidyCheck> const& check, Compilation const& compilation,
                       Diagnostics const& diagnostics) {

    DiagnosticEngine diagEngine(*compilation.getSourceManager());
    diagEngine.setMessage(check->diagCode(), check->diagMessage());
    diagEngine.setSeverity(check->diagCode(), check->diagSeverity());
    
    auto & diags = check->getDiagnostics();

    auto client = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(client);

    for (auto& diag : diags) {
        diagEngine.issue(diag);
    }

    return client->getString();
}

TEST_CASE("Undriven range: simple case with a two bit bus") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  logic [1:0] a;
  always_comb
    a[0] = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);

    Registry::setSourceManager(compilation.getSourceManager());
    auto check = Registry::create("UndrivenRange");

    CHECK_FALSE(check->check(root));

    std::string result = "\n" + reportDiagnostics(check, compilation, diagnostics);
    CHECK(result == R"(
source:3:15: warning: [SYNTHESIS-20] variable a has undriven bits: 1
  logic [1:0] a;
              ^
)");
}

TEST_CASE("Undriven range: a 32b bus with missing drivers") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  logic [31:0] a;
  always_comb begin
    a[7:0] = 8'hFF;
    a[11] = 1;
    a[30] = 0;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());

    auto check = Registry::create("UndrivenRange");
    CHECK_FALSE(check->check(root));

    std::string result = "\n" + reportDiagnostics(check, compilation, diagnostics);
    CHECK(result == R"(
source:3:16: warning: [SYNTHESIS-20] variable a has undriven bits: 8:10, 12:29, 31
  logic [31:0] a;
               ^
)");
}

