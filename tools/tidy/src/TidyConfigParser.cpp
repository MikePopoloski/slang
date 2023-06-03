//------------------------------------------------------------------------------
//! @file TidyConfigParser.cpp
//! @brief Parser of the config file for the slang-tidy tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "TidyConfigParser.h"

#include "fmt/format.h"
#include <fstream>
#include <iostream>

#include "slang/util/OS.h"
#include "fmt/color.h"

TidyConfigParser::TidyConfigParser(const std::string_view path) {
    parserState = ParserState::Initial;
    filePath = path;
    fileStream << std::ifstream(filePath).rdbuf();
    line = 0;
    col = 0;
    parse_file();
}

TidyConfigParser::TidyConfigParser(const std::string &config) {
    parserState = ParserState::Initial;
    filePath = "raw-string";
    fileStream.str(config);
    line = 0;
    col = 0;
    parse_file();
}

char TidyConfigParser::next_char() {
    char c;
    do {
        fileStream >> std::noskipws >> c;
    } while (c == ' ' || c == '\t');
    if (fileStream.eof())
        return 0;
    col++;
#if defined(_WIN32)
    if (c == '\r' && stream.peek() == '\n') {
        stream >> std::noskipws >> c;
        line++
    }
#elif defined(_MACOS)
    if (c == '\r') {
        c = '\n';
        line++;
    }
#else
    if (c == '\n') {
        line++;
    }
#endif
    return c;
}

inline char TidyConfigParser::peek_char() {
    return static_cast<char>(fileStream.peek());
}

void TidyConfigParser::parse_file() {
    while (!fileStream.eof()) {
        switch (parserState) {
            case ParserState::Initial:
                parse_initial();
                break;
            case ParserState::ParsingChecks:
                parse_checks();
                break;
            case ParserState::ParsingCheckConfigs:
                parse_check_configs();
                break;
        }
    }
}

void TidyConfigParser::parse_initial() {
    char currentChar = next_char();
    if (currentChar == 0)
        report_error_and_exit("Unexpected end of file");

    if (!isalpha(currentChar))
        report_error_and_exit(fmt::format("Unexpected token with ascii_code ({}): {}", +currentChar, currentChar));

    std::string str;
    while (!fileStream.eof() && isalpha(currentChar)) {
        str.push_back(currentChar);
        currentChar = next_char();
    }

    if (currentChar != ':')
        report_error_and_exit(fmt::format("Expected token: ':', found: ({}){}", +currentChar, currentChar));

    if (auto keyword = keywords.find(str); keyword != keywords.end()) {
        switch (keyword->second) {
            case Keywords::ChecksKeyword:
                parserState = ParserState::ParsingChecks;
                break;
            case Keywords::CheckConfigs:
                parserState = ParserState::ParsingCheckConfigs;
                break;
        }
    } else {
        report_error_and_exit(fmt::format("Expected a keyword found: {}", str));
    }
}

void TidyConfigParser::parse_checks() {
    while (!fileStream.eof()) {
        TidyConfig::CheckStatus newCheckState = TidyConfig::CheckStatus::ENABLED;
        bool checkGroupParsed = false;
        bool ruleParsed = false;
        std::string checkGroup;
        std::string checkName;

        // Get the first char
        char currentChar = next_char();

        // If it is a new line ignore it and get the following char
        if (currentChar == '\n')
            currentChar = next_char();

        if (currentChar == '-')
            newCheckState = TidyConfig::CheckStatus::DISABLED;
        else if (isalpha(currentChar))
            checkGroup.push_back(currentChar);
        else if (currentChar == '*') {
            if (checkGroup.size())
                report_error_and_exit("Unexpected '*'");
            toggle_all_checks(TidyConfig::CheckStatus::ENABLED);
            currentChar = next_char();
            if (currentChar == '\n' || currentChar == 0) {
                parserState = TidyConfigParser::ParserState::Initial;
                return;
            } else if (currentChar == ',') {
                currentChar = next_char();
                if (currentChar != '\n') {
                    report_error_and_exit(
                            fmt::format("Expected new line but found: ({}){}", +currentChar, currentChar));
                }
                continue;
            } else {
                report_error_and_exit(fmt::format("Expected ',' but found: ({}){}", +currentChar, currentChar));
            }
        } else {
            report_error_and_exit(
                    fmt::format("Expected '-' or '*' or a letter but found: ({}){}", +currentChar, currentChar));
        }

        if (ruleParsed)
            continue;

        // Parse second char
        currentChar = next_char();

        if (currentChar == '*') {
            if (checkGroup.size())
                report_error_and_exit("Unexpected '*'");
            ruleParsed = true;
            toggle_all_checks(TidyConfig::CheckStatus::DISABLED);
        } else if (currentChar == '-')
            checkGroupParsed = true;
        else if (isalpha(currentChar))
            checkGroup.push_back(currentChar);
        else {
            report_error_and_exit(
                    fmt::format("Expected '*' or a letter but found: ({}){}", +currentChar, currentChar));
        }

        if (ruleParsed) {
            currentChar = next_char();
            if (currentChar == '\n' || currentChar == 0) {
                parserState = TidyConfigParser::ParserState::Initial;
                return;
            } else if (currentChar != ',') {
                report_error_and_exit(fmt::format("Expected ',' but found: ({}){}", +currentChar, currentChar));
            }
            continue;
        }

        // Parse group name
        while (!checkGroupParsed) {
            currentChar = next_char();
            if (currentChar == '-')
                checkGroupParsed = true;
            else if (isalpha(currentChar))
                checkGroup.push_back(currentChar);
            else {
                report_error_and_exit(
                        fmt::format("Expected '-' or a letter but found: ({}){}", +currentChar, currentChar));
            }
        }

        // Parse check name
        bool checkParsed = false;
        while (true) {
            currentChar = next_char();
            if (currentChar == ',') {
                toggle_check(checkGroup, checkName, newCheckState);
                if (next_char() != '\n') {
                    report_error_and_exit(
                            fmt::format("Expected new line but found: ({}){}", +currentChar, currentChar));
                }
                break;
            } else if (currentChar == '*') {
                if (checkName.size())
                    report_error_and_exit("Unexpected '*'");
                toggle_all_group_checks(checkGroup, newCheckState);
                checkParsed = true;
            } else if (isalpha(currentChar) || currentChar == '-') {
                checkName.push_back(currentChar);
            } else if (currentChar == '\n' || currentChar == 0) {
                if (!checkParsed)
                    toggle_check(checkGroup, checkName, newCheckState);
                parserState = ParserState::Initial;
                return;
            } else {
                report_error_and_exit(fmt::format("Unexpected ({}){}", +currentChar, currentChar));
            }
        }
    }
}

void TidyConfigParser::parse_check_configs() {
    while (!fileStream.eof()) {
        std::string optionName;
        std::string optionValue;

        // Parse optional newline
        if (peek_char() == '\n')
            next_char();

        // Parse option name
        while (true) {
            char currentChar = next_char();
            if (currentChar == ':')
                break;
            else if (isalpha(currentChar))
                optionName.push_back(currentChar);
            else
                report_error_and_exit(
                        fmt::format("Expected ':' or '_' or a letter but found ({}){}", +currentChar, currentChar));
        }

        // Parse option value
        while (true) {
            char currentChar = next_char();
            if (currentChar == ',') {
                set_check_config(optionName, optionValue);
                if (next_char() != '\n') {
                    report_error_and_exit(
                            fmt::format("Expected new line but found: ({}){}", +currentChar, currentChar));
                }
                break;
            } else if (isalpha(currentChar) || currentChar == '_') {
                optionValue.push_back(currentChar);
            } else if (currentChar == '\n' || currentChar == 0) {
                set_check_config(optionName, optionValue);
                parserState = ParserState::Initial;
                return;
            } else
                report_error_and_exit(
                        fmt::format("Expected ',' new line or a letter but found ({}){}", +currentChar, currentChar));
        }
    }
}

void TidyConfigParser::toggle_all_checks(TidyConfig::CheckStatus status) {
    config.toggle_all(status);
}

void TidyConfigParser::toggle_all_group_checks(const std::string &groupName, TidyConfig::CheckStatus status) {
    auto kind = slang::tidy_kind_from_str(groupName);
    if (!kind)
        report_error_and_exit(fmt::format("Group {} does not exist", groupName));

    config.toggle_group(kind.value(), status);
}

void TidyConfigParser::toggle_check(const std::string &groupName, const std::string &checkName,
                                    TidyConfig::CheckStatus status) {
    if (checkName.empty()) {
        report_warning(
                fmt::format("Empty check name in group {0}, you can toggle the whole group with {0}-*", groupName)
        );
        return;
    }

    auto kind = slang::tidy_kind_from_str(groupName);
    if (!kind)
        report_error_and_exit(fmt::format("Group {} does not exist", groupName));
    bool found = config.toggle_check(kind.value(), format_check_name(checkName), status);

    if (!found)
        report_warning(
                fmt::format("Check name {} does not exist in group {}", checkName, groupName));
}

void TidyConfigParser::set_check_config(const std::string &configName, std::string configValue) {
    auto set_config = [&](auto value) {
        try {
            config.set_config(configName, value);
        }
        catch (std::invalid_argument &exception) {
            report_warning(exception.what());
        }
    };

    std::transform(configValue.begin(), configValue.end(), configValue.begin(), ::tolower);

    if (configValue == "true" || configValue == "false") {
        set_config(configValue == "true" ? true : false);
    } else {
        set_config(configValue);
    }
}

void TidyConfigParser::report_error_and_exit(const std::string &str) const {
    slang::OS::printE(fmt::format("Error while parsing slang-tidy config: {} "
                                  "{}:{}\n\t{}\n",
                                  filePath, line, col, str));
    exit(1);
}

void TidyConfigParser::report_warning(const std::string &str) const {
    slang::OS::print(fmt::format("Warning while parsing slang-tidy config: {} "
                                 "{}:{}\n\t{}\n",
                                 filePath, line, col, str));
}

std::string TidyConfigParser::format_check_name(const std::string &checkName) {
    if (checkName.empty())
        return "";
    std::string capitalizedName;
    capitalizedName.resize(checkName.size());
    std::transform(checkName.begin(), checkName.end(), capitalizedName.begin(), ::tolower);
    // Input string is expected to have the format a-b-c-d-e...
    // Capitalize the first letter
    capitalizedName[0] = static_cast<char>(::toupper(capitalizedName[0]));
    if (std::count(capitalizedName.begin(), capitalizedName.end(), '-') == 0) {
        // If there are no '-' on the name, we are done
        return capitalizedName;
    }

    // Find all the '-' and capitalize the following char if exists
    auto nameLength = checkName.size();
    size_t pos = 0;
    while (true) {
        pos = capitalizedName.find('-', pos);
        // If pos+1 does not exist, or we have not found anymore '-' we can break.
        // Else capitalize the pos+1 letter
        if (pos == std::string::npos || nameLength <= pos)
            break;
        else {
            capitalizedName[pos + 1] = static_cast<char>(::toupper(capitalizedName[pos + 1]));
            pos += 1;
        }
    }

    // At this point the string should have the format Aa-Bb-Cc-....
    // Remove the '-' from the string and we are done
    size_t currentPos = 0;
    size_t nextPos = capitalizedName.find('-');
    std::string name;
    while (nextPos != std::string::npos) {
        name.append(capitalizedName.substr(currentPos, nextPos - currentPos));
        currentPos = nextPos + 1;
        nextPos = capitalizedName.find('-', currentPos);
    }
    name.append(capitalizedName.substr(currentPos));
    return name;
}
