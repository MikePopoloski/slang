// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyConfigParser.h"
#include "TidyFactory.h"

#include "slang/diagnostics/Diagnostics.h"

TEST_CASE("TidyParser: Enable all") {
    auto config_str = std::string(R"(Checks: *)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Disable all") {
    auto config_str = std::string(R"(Checks: -*)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable specific test") {
    auto config_str = std::string(R"(Checks:
    -*,
    style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
}

TEST_CASE("TidyParser: Disable specific test") {
    auto config_str = std::string(R"(Checks:
    -style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
}

TEST_CASE("TidyParser: Disable specific kind") {
    auto config_str = std::string(R"(Checks:
    -synthesis-*)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable specific kind") {
    auto config_str = std::string(R"(Checks:
    -*,
    synthesis-*)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Enable some checks") {
    auto config_str = std::string(R"(Checks:
    -*,
    synthesis-only-assigned-on-reset,
    style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Disable some checks") {
    auto config_str = std::string(R"(Checks:
    -synthesis-only-assigned-on-reset,
    -style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Set check config") {
    auto config_str = std::string(R"(CheckConfigs:
    clkName: clk,
    clkNameRegexString: "clock\S.*",
    resetIsActiveHigh: false,
    inputPortSuffix: _k,
    inputPortSuffix: _p)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.getCheckConfigs().clkName == "clk");
    CHECK(config.getCheckConfigs().resetName == "rst_ni");
    CHECK(config.getCheckConfigs().clkNameRegexString == "clock\\S.*");
    CHECK_FALSE(config.getCheckConfigs().resetIsActiveHigh);
    CHECK(config.getCheckConfigs().inputPortSuffix == std::vector<std::string>{"_p"});
}

TEST_CASE("TidyParser: CheckConfigs and Checks") {
    auto config_str = std::string(R"(CheckConfigs:
        clkName: clk,
        resetIsActiveHigh: false,
        inputPortSuffix: _k,
        inputPortSuffix: _p
    Checks:
        -synthesis-only-assigned-on-reset,
        -style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.getCheckConfigs().clkName == "clk");
    CHECK(config.getCheckConfigs().resetName == "rst_ni");
    CHECK_FALSE(config.getCheckConfigs().resetIsActiveHigh);
    CHECK(config.getCheckConfigs().inputPortSuffix == std::vector<std::string>{"_p"});
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Checks and CheckConfigs") {
    auto config_str = std::string(R"(Checks:
        -synthesis-only-assigned-on-reset,
        -style-enforce-port-suffix




    CheckConfigs:
        clkName: clk,
        resetIsActiveHigh: false,
        inputPortSuffix: _k,
        inputPortSuffix: _p





)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.getCheckConfigs().clkName == "clk");
    CHECK(config.getCheckConfigs().resetName == "rst_ni");
    CHECK_FALSE(config.getCheckConfigs().resetIsActiveHigh);
    CHECK(config.getCheckConfigs().inputPortSuffix == std::vector<std::string>{"_p"});
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "RegisterHasNoReset"));
}

TEST_CASE("TidyParser: Parse array") {
    auto config_str = std::string(R"(CheckConfigs:
        inputPortSuffix: [_a, _b, _c],
        inoutPortSuffix: [_a],
        outputPortSuffix: []
)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.getCheckConfigs().inputPortSuffix == std::vector<std::string>{"_a", "_b", "_c"});
    CHECK(config.getCheckConfigs().inoutPortSuffix == std::vector<std::string>{"_a"});
    CHECK(config.getCheckConfigs().outputPortSuffix == std::vector<std::string>{});
}

TEST_CASE("TidyParser: Support for moduleInstantiationPrefix") {
    auto config_str = std::string(R"(CheckConfigs:
    clkName: clock,
    inputPortSuffix: ,
    outputPortSuffix: ,
    moduleInstantiationPrefix: asdf,
    resetIsActiveHigh: true)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();
    CHECK(config.getCheckConfigs().moduleInstantiationPrefix == "asdf");
}

TEST_CASE("TidyParser: existing checker in the wrong group") {
    auto config_str = std::string(R"(Checks:
    -style-enforce-port-suffix)");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "EnforcePortSuffix"));
}

TEST_CASE("TidyParser: single check error severity") {
    auto config_str = std::string(R"(Checks:
  synthesis-only-assigned-on-reset=error)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "OnlyAssignedOnReset"));
    CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis, "OnlyAssignedOnReset") ==
          slang::DiagnosticSeverity::Error);
}

TEST_CASE("TidyParser: single group error severity") {
    auto config_str = std::string(R"(Checks:
  -*,
  synthesis-*=error)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();
    Registry::setConfig(config);

    for (auto const& check : Registry::getEnabledChecks()) {
        CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis, check) ==
              slang::DiagnosticSeverity::Error);
    }
}

TEST_CASE("TidyParser: single check various severities") {
    auto config_str = std::string(R"(Checks:
  synthesis-undriven-range=ignored,
  synthesis-always-f-f-assignment-outside-conditional=note,
  synthesis-unused-sensitive-signal=warning,
  style-no-legacy-generate=error,
  style-no-dot-var-in-port-connection=fatal
)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();

    CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis, "UndrivenRange") ==
          slang::DiagnosticSeverity::Ignored);
    CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis,
                                  "AlwaysFFAssignmentOutsideConditional") ==
          slang::DiagnosticSeverity::Note);
    CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis, "UnusedSensitiveSignal") ==
          slang::DiagnosticSeverity::Warning);
    CHECK(config.getCheckSeverity(slang::TidyKind::Style, "NoLegacyGenerate") ==
          slang::DiagnosticSeverity::Error);
    CHECK(config.getCheckSeverity(slang::TidyKind::Style, "NoDotVarInPortConnection") ==
          slang::DiagnosticSeverity::Fatal);
}
