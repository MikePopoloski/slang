// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyConfigParser.h"
#include "TidyFactory.h"

#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/OS.h"

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
    inputPortSuffix: _p,
    covergroupRegexString: "^covergroup_\S*",
    coverpointRegexString: "^coverpoint_\S*",
    crossRegexString: "^cross_coverpoint_\S*",
    enumRegexString: "[a-z_0-9]+_e",
    structRegexString: "[a-z_0-9]+_s",
    unionRegexString: "[a-z_0-9]+_u",
    typedefRegexString: "[a-z_0-9]+_t")");
    TidyConfigParser parser(config_str);

    auto config = parser.getConfig();

    CHECK(config.getCheckConfigs().clkName == "clk");
    CHECK(config.getCheckConfigs().resetName == "rst_ni");
    CHECK(config.getCheckConfigs().clkNameRegexString == "clock\\S.*");
    CHECK_FALSE(config.getCheckConfigs().resetIsActiveHigh);
    CHECK(config.getCheckConfigs().inputPortSuffix == std::vector<std::string>{"_p"});
    CHECK(config.getCheckConfigs().covergroupRegexString == "^covergroup_\\S*");
    CHECK(config.getCheckConfigs().coverpointRegexString == "^coverpoint_\\S*");
    CHECK(config.getCheckConfigs().crossRegexString == "^cross_coverpoint_\\S*");
    CHECK(config.getCheckConfigs().enumRegexString == "[a-z_0-9]+_e");
    CHECK(config.getCheckConfigs().structRegexString == "[a-z_0-9]+_s");
    CHECK(config.getCheckConfigs().unionRegexString == "[a-z_0-9]+_u");
    CHECK(config.getCheckConfigs().typedefRegexString == "[a-z_0-9]+_t");
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

TEST_CASE("TidyParser: check names with acronyms") {
    auto guard = OS::captureOutput();
    auto config_str = std::string(R"(Checks:
    -*,
    style-always-ff-blocking=error,
    synthesis-always-ff-assignment-outside-conditional,
    style-only-ansi-port-decl)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "AlwaysFFBlocking"));
    CHECK(config.getCheckSeverity(slang::TidyKind::Style, "AlwaysFFBlocking") ==
          slang::DiagnosticSeverity::Error);
    CHECK(
        config.isCheckEnabled(slang::TidyKind::Synthesis, "AlwaysFFAssignmentOutsideConditional"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "OnlyANSIPortDecl"));
    CHECK(OS::capturedStdout.empty());
}

TEST_CASE("TidyParser: deprecated check names with split acronyms") {
    // Names generated before acronyms were kept together are still accepted
    auto guard = OS::captureOutput();
    auto config_str = std::string(R"(Checks:
    -*,
    style-always-f-f-blocking,
    style-only-a-n-s-i-port-decl)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();

    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "AlwaysFFBlocking"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Style, "OnlyANSIPortDecl"));
    CHECK(OS::capturedStdout.find("use style-always-ff-blocking instead") != std::string::npos);
    CHECK(OS::capturedStdout.find("use style-only-ansi-port-decl instead") != std::string::npos);
}

TEST_CASE("TidyParser: check names are printed with acronyms kept together") {
    CHECK(TidyConfigParser::unformatCheckName("AlwaysFFBlocking") == "always-ff-blocking");
    CHECK(TidyConfigParser::unformatCheckName("OnlyANSIPortDecl") == "only-ansi-port-decl");
    CHECK(TidyConfigParser::unformatCheckName("EnforcePortSuffix") == "enforce-port-suffix");
    CHECK(TidyConfigParser::unformatCheckName("NoCaseX") == "no-case-x");
}

TEST_CASE("TidyParser: comments") {
    auto config_str = std::string(R"(# Project slang-tidy configuration

Checks:
    # Style checks the design doesn't follow
    -style-generate-named, # legacy code
    -style-no-legacy-generate,
    # synthesis-no-latches-on-design=error,

    synthesis-register-has-no-reset=error # catches missing resets
# End of checks

CheckConfigs:
    # Clock and reset
    clkName: clk_i, # main clock

    # resetName: rst_x,
    resetIsActiveHigh: true
# Trailing comment)");
    TidyConfigParser parser(config_str);
    auto config = parser.getConfig();

    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "GenerateNamed"));
    CHECK_FALSE(config.isCheckEnabled(slang::TidyKind::Style, "NoLegacyGenerate"));
    CHECK(config.isCheckEnabled(slang::TidyKind::Synthesis, "NoLatchesOnDesign"));
    CHECK_FALSE(config.getCheckSeverity(slang::TidyKind::Synthesis, "NoLatchesOnDesign"));
    CHECK(config.getCheckSeverity(slang::TidyKind::Synthesis, "RegisterHasNoReset") ==
          slang::DiagnosticSeverity::Error);
    CHECK(config.getCheckConfigs().clkName == "clk_i");
    CHECK(config.getCheckConfigs().resetName == "rst_ni");
    CHECK(config.getCheckConfigs().resetIsActiveHigh);
}
