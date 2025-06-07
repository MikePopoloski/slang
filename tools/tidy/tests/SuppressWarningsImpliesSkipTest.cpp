//------------------------------------------------------------------------------
//! @file SuppressWarningsImpliesSkipTest.cpp
//! @brief Test that --suppress-warnings implies --skip-file functionality
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Test.h"
#include "TidyConfig.h"

#include "slang/driver/Driver.h"
#include "slang/text/Glob.h"

// Test that --suppress-warnings patterns are automatically added as skip patterns in slang-tidy
TEST_CASE("Suppress warnings implies skip patterns") {
    using namespace slang;
    using namespace slang::driver;

    // Create a driver and add the suppress-warnings pattern
    Driver driver;
    driver.addStandardArgs();

    // Simulate adding a pattern to suppress-warnings
    std::error_code ec = driver.diagEngine.addIgnorePaths("test_*.sv");
    REQUIRE(!ec);

    // Verify that the ignore patterns were added
    auto ignorePaths = driver.diagEngine.getIgnorePaths();
    REQUIRE(ignorePaths.size() == 1);

    // Create a TidyConfig and simulate the logic in tidy.cpp that adds
    // suppress-warnings patterns as skip patterns
    TidyConfig tidyConfig;
    tidyConfig.addSkipPattern(
        std::vector<std::filesystem::path>(ignorePaths.begin(), ignorePaths.end()));

    // Verify that the pattern was added to skip patterns
    auto skipPatterns = tidyConfig.getSkipPatterns();
    REQUIRE(skipPatterns.size() == 1);

    // Test that pattern matching works with svGlobMatches
    auto testPath = std::filesystem::path("test_file.sv");
    CHECK(slang::svGlobMatches(testPath, skipPatterns[0]));

    auto nonMatchingPath = std::filesystem::path("other_file.sv");
    CHECK_FALSE(slang::svGlobMatches(nonMatchingPath, skipPatterns[0]));
}

TEST_CASE("TidyConfig addSkipPattern functionality") {
    using namespace slang;

    // Create a TidyConfig and test pattern functionality
    TidyConfig config;

    // Test adding single pattern
    config.addSkipPattern(std::filesystem::path("test_*.sv"));
    auto patterns = config.getSkipPatterns();
    REQUIRE(patterns.size() == 1);

    // Test adding multiple patterns
    std::vector<std::filesystem::path> morePatterns = {std::filesystem::path("vendor_*.sv"),
                                                       std::filesystem::path("third_party_*.v")};
    config.addSkipPattern(morePatterns);
    patterns = config.getSkipPatterns();
    REQUIRE(patterns.size() == 3);

    // Verify pattern matching works
    CHECK(slang::svGlobMatches(std::filesystem::path("test_module.sv"), patterns[0]));
    CHECK(slang::svGlobMatches(std::filesystem::path("vendor_ip.sv"), patterns[1]));
    CHECK(slang::svGlobMatches(std::filesystem::path("third_party_lib.v"), patterns[2]));

    // Verify non-matching patterns
    CHECK_FALSE(slang::svGlobMatches(std::filesystem::path("my_module.sv"), patterns[0]));
    CHECK_FALSE(slang::svGlobMatches(std::filesystem::path("my_module.sv"), patterns[1]));
    CHECK_FALSE(slang::svGlobMatches(std::filesystem::path("my_module.sv"), patterns[2]));
}
