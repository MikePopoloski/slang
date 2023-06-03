//------------------------------------------------------------------------------
//! @file TidyConfigParser.h
//! @brief Parser of the config file for the slang-tidy tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfig.h"
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>

class TidyConfigParser {
public:
    explicit TidyConfigParser(const std::string_view path);
    explicit TidyConfigParser(const std::string& config);
    [[nodiscard]] TidyConfig getConfig() const { return config; };

private:
    /// Reserved keywords of the tidy config parser language
    enum class Keywords { ChecksKeyword, CheckConfigs };
    /// Internal states of the tidy config parser
    enum class ParserState { Initial, ParsingChecks, ParsingCheckConfigs };

    const std::unordered_map<std::string, Keywords> keywords = {
        {"Checks", Keywords::ChecksKeyword}, {"CheckConfigs", Keywords::CheckConfigs}};

    ParserState parserState;
    std::string filePath;
    std::stringstream fileStream;
    uint64_t line;
    uint64_t col;

    TidyConfig config;

    /// Reports an error and terminates the program
    void report_error_and_exit(const std::string& str) const;
    /// Reports a warning
    void report_warning(const std::string& str) const;

    /// Parses the whole file and populates the config object
    void parse_file();
    /// Gets the next character from the file stream, skips whitespaces and tabs
    char next_char();
    /// Peeks the next character from the file stream
    char peek_char();
    /// Parses config file and sets the state to parse checks or check configs
    void parse_initial();
    /// Parsers the check regions of the config file
    void parse_checks();
    /// Parses the check configs regions of the config file
    void parse_check_configs();
    /// Toggles all checks with the status provided
    void toggle_all_checks(TidyConfig::CheckStatus status);
    /// Toggles all checks in the specified group with the status provided
    void toggle_all_group_checks(const std::string& groupName, TidyConfig::CheckStatus status);
    /// Toggles the specified check with the status provided
    void toggle_check(const std::string& groupName, const std::string& checkName, TidyConfig::CheckStatus status);
    /// Sets the check config with the provided value
    void set_check_config(const std::string &configName, std::string configValue);

    /// The name format of the checks provided by the user are required to be: this-is-my-check
    /// but the registered names in the TidyFactory are ThisIsMyCheck. This function translates from
    /// the one provided by the user to the one expected by the Factory.
    static std::string format_check_name(const std::string& checkName);
};
