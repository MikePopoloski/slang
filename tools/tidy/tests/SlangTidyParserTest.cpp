//------------------------------------------------------------------------------
//! @file SlangTidyParserTest.h
//! @brief Test suite for the SlangTidyParser
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Test.h"
#include "TidyConfigParser.h"

TEST_CASE("TidyParser: Enable all") {
    auto config_str = std::string(R"(Checks: *)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Disable all") {
    auto config_str = std::string(R"(Checks: -*)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable specific test") {
    auto config_str = std::string(R"(Checks:
    -*,
    ports-enforce-port-suffix)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
}

TEST_CASE("TidyParser: Disable specific test") {
    auto config_str = std::string(R"(Checks:
    -ports-enforce-port-suffix)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
}

TEST_CASE("TidyParser: Disable specific kind") {
    auto config_str = std::string(R"(Checks:
    -synthesis-*)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable specific kind") {
    auto config_str = std::string(R"(Checks:
    -*,
    synthesis-*)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable some checks") {
    auto config_str = std::string(R"(Checks:
    -*,
    synthesis-only-assigned-on-reset,
    ports-enforce-port-suffix)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Disable some checks") {
    auto config_str = std::string(R"(Checks:
    -synthesis-only-assigned-on-reset,
    -ports-enforce-port-suffix)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Set check config") {
    auto config_str = std::string(R"(CheckConfigs:
    clkName: clk,
    resetIsActiveHigh: false,
    inputPortSuffix: _k,
    inputPortSuffix: _p)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.get_check_configs().clkName == "clk");
    CHECK(config.get_check_configs().resetName == "rst_ni");
    CHECK_FALSE(config.get_check_configs().resetIsActiveHigh);
    CHECK(config.get_check_configs().inputPortSuffix == "_p");
}

TEST_CASE("TidyParser: CheckConfigs and Checks") {
    auto config_str = std::string(R"(CheckConfigs:
        clkName: clk,
        resetIsActiveHigh: false,
        inputPortSuffix: _k,
        inputPortSuffix: _p
    Checks:
        -synthesis-only-assigned-on-reset,
        -ports-enforce-port-suffix)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.get_check_configs().clkName == "clk");
    CHECK(config.get_check_configs().resetName == "rst_ni");
    CHECK_FALSE(config.get_check_configs().resetIsActiveHigh);
    CHECK(config.get_check_configs().inputPortSuffix == "_p");
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Checks and CheckConfigs") {
    auto config_str = std::string(R"(Checks:
        -synthesis-only-assigned-on-reset,
        -ports-enforce-port-suffix
    CheckConfigs:
        clkName: clk,
        resetIsActiveHigh: false,
        inputPortSuffix: _k,
        inputPortSuffix: _p)"
    );
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.get_check_configs().clkName == "clk");
    CHECK(config.get_check_configs().resetName == "rst_ni");
    CHECK_FALSE(config.get_check_configs().resetIsActiveHigh);
    CHECK(config.get_check_configs().inputPortSuffix == "_p");
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Ports, "EnforcePortSuffix"));
    CHECK_FALSE(config.is_check_enabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.is_check_enabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}
