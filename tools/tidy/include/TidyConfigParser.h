//------------------------------------------------------------------------------
//! @file TidyConfigParser.h
//! @brief Parser of the config file for the slang-tidy tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfig.h"
#include <filesystem>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>

class TidyConfigParser {
public:
    explicit TidyConfigParser(const std::filesystem::path& path);

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
    void reportErrorAndExit(const std::string& str) const;

    /// Reports a warning
    void reportWarning(const std::string& str) const;

    /// Parses the whole file and populates the config object
    void parseFile();

    /// Gets the next character from the file stream, skips whitespaces and tabs
    char nextChar();

    /// Peeks the next character from the file stream, skips whitespaces and tabs
    char peekChar();

    /// Reads characters from the file stream and adds them to str
    /// as long as pred for the extracted character is true.
    /// Returns the first character for which pred is false.
    template<typename Func, std::enable_if_t<std::is_invocable_r_v<bool, Func, char>, bool> = true>
    char readIf(std::string& str, Func pred) {
        char c;
        while (pred(c = nextChar())) {
            str.push_back(c);
        }
        return c;
    }

    /// Parses config file and sets the state to parse checks or check configs
    void parseInitial();

    /// Parsers the check regions of the config file
    void parseChecks();

    /// Parses the check configs regions of the config file
    void parseCheckConfigs();

    /// Parses multiple configValues by individually
    /// parsing every single config values of type T
    template<typename T>
    void parseConfigValue(std::vector<T>& config, std::vector<std::string>&& configValues) {
        config.clear();
        for (auto& value : configValues) {
            T tmp;
            parseConfigValue(tmp, std::move(value));
            config.emplace_back(std::move(tmp));
        }
    }

    /// Parses configValue as a single string
    void parseConfigValue(std::string& config, std::string&& configValue);

    /// Parses configValue as a bool.
    void parseConfigValue(bool& config, std::string&& configValue);

    /// Toggles all checks with the status provided
    void toggleAllChecks(TidyConfig::CheckStatus status);

    /// Toggles all checks in the specified group with the status provided
    void toggleAllGroupChecks(const std::string& groupName, TidyConfig::CheckStatus status);

    /// Toggles the specified check with the status provided
    void toggleCheck(const std::string& groupName, const std::string& checkName,
                     TidyConfig::CheckStatus status);

    /// Sets the check config with the provided value
    void setCheckConfig(const std::string& configName, std::vector<std::string> configValue);

    /// The name format of the checks provided by the user are required to be: this-is-my-check
    /// but the registered names in the TidyFactory are ThisIsMyCheck. This function translates from
    /// the one provided by the user to the one expected by the Factory.
    static std::string formatCheckName(const std::string& checkName);
};
