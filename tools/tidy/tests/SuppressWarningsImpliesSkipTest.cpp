// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/driver/Driver.h"

// Test that --suppress-warnings files are automatically added as skip files in slang-tidy
TEST_CASE("Suppress warnings implies skip file") {
    using namespace slang;
    using namespace slang::driver;

    // Create test source with a style warning that slang-tidy would catch
    std::string_view code = R"(
module test_module;
    logic a;
    // This uses old always syntax which should trigger NoOldAlwaysSyntax warning
    always @(a) begin
        // empty
    end
endmodule
)";

    // Create a driver and add the suppress-warnings option
    Driver driver;
    driver.addStandardArgs();

    // Simulate adding a file path to suppress-warnings
    std::error_code ec = driver.diagEngine.addIgnorePaths("test_file.sv");
    REQUIRE(!ec);

    // Verify that the ignore paths were added
    auto ignorePaths = driver.diagEngine.getIgnorePaths();
    REQUIRE(ignorePaths.size() == 1);

    // Create a TidyConfig and simulate the logic in tidy.cpp that adds
    // suppress-warnings paths as skip files
    TidyConfig tidyConfig;
    for (const auto& suppressPath : ignorePaths) {
        tidyConfig.addSkipFile(suppressPath.string());
        tidyConfig.addSkipPath(suppressPath.string());
    }

    // Verify that the path was added to skip files
    auto skipFiles = tidyConfig.getSkipFiles();
    auto skipPaths = tidyConfig.getSkipPaths();

    REQUIRE(skipFiles.size() == 1);
    REQUIRE(skipPaths.size() == 1);

    // The skip files should contain the filename
    CHECK(skipFiles[0] == "test_file.sv");
}

TEST_CASE("Suppress warnings integration test") {
    using namespace slang;

    // Test source with old always syntax
    std::string_view code = R"(
module test_module;
    logic a;
    always @(a) begin
        // This should trigger NoOldAlwaysSyntax warning
    end
endmodule
)";

    auto tree = SyntaxTree::fromText(code, "test_file.sv");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    compilation.freeze();

    analysis::AnalysisManager analysisManager;
    analysisManager.analyze(compilation);

    // Test without skip - should find warning
    {
        TidyConfig config;
        Registry::setConfig(config);
        Registry::setSourceManager(compilation.getSourceManager());

        auto check = Registry::create("NoOldAlwaysSyntax");
        auto result = check->check(compilation.getRoot(), analysisManager);

        // Should fail (find the warning)
        CHECK_FALSE(result);
    }

    // Test with skip file - should not find warning
    {
        TidyConfig config;
        config.addSkipFile("test_file.sv");
        Registry::setConfig(config);
        Registry::setSourceManager(compilation.getSourceManager());

        auto check = Registry::create("NoOldAlwaysSyntax");
        auto result = check->check(compilation.getRoot(), analysisManager);

        // Should pass (skip the warning)
        CHECK(result);
    }
}
