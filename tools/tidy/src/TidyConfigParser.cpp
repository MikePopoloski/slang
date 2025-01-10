// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyConfigParser.h"

#include "fmt/format.h"
#include <fstream>

#include "slang/util/OS.h"

template<typename T>
struct is_vector : std::false_type {};

template<typename T>
struct is_vector<std::vector<T>> : std::true_type {};

template<typename T>
inline constexpr bool is_vector_v = is_vector<T>::value;

TidyConfigParser::TidyConfigParser(const std::filesystem::path& path) {
    parserState = ParserState::Initial;
    filePath = path.string();
    fileStream << std::ifstream(filePath).rdbuf();
    line = 0;
    col = 0;
    parseFile();
}

TidyConfigParser::TidyConfigParser(const std::string& config) {
    parserState = ParserState::Initial;
    filePath = "raw-string";
    fileStream.str(config);
    line = 0;
    col = 0;
    parseFile();
}

char TidyConfigParser::nextChar() {
    char c;
    do {
        fileStream >> std::noskipws >> c;
        if (fileStream.eof())
            return 0;
    } while (c == ' ' || c == '\t');
    col++;
#if defined(_WIN32)
    if (c == '\r' && fileStream.peek() == '\n') {
        fileStream >> std::noskipws >> c;
        col = 0;
        line++;
    }
#elif defined(_MACOS)
    if (c == '\r') {
        c = '\n';
        col = 0;
        line++;
    }
#else
    if (c == '\n') {
        col = 0;
        line++;
    }
#endif
    return c;
}

inline char TidyConfigParser::peekChar() {
    while (fileStream.peek() == ' ' || fileStream.peek() == '\t') {
        fileStream.get();
    }
    if (fileStream.eof())
        return 0;
#if defined(_WIN32)
    char ret = fileStream.peek();
    if (ret == '\r') {
        fileStream.get();
        if (fileStream.peek() == '\n') {
            ret = '\n';
        }
        fileStream.unget();
    }
    return ret;
#elif defined(_MACOS)
    char ret = fileStream.peek();
    if (ret == '\r')
        ret = '\n';
    return ret;
#else
    return static_cast<char>(fileStream.peek());
#endif
}

void TidyConfigParser::parseFile() {
    while (!fileStream.eof()) {
        switch (parserState) {
            case ParserState::Initial:
                parseInitial();
                break;
            case ParserState::ParsingChecks:
                parseChecks();
                break;
            case ParserState::ParsingCheckConfigs:
                parseCheckConfigs();
                break;
        }
    }
}

void TidyConfigParser::parseInitial() {
    char currentChar = peekChar();
    if (currentChar == 0)
        reportErrorAndExit("Unexpected end of file");

    if (!isalpha(currentChar))
        reportErrorAndExit(
            fmt::format("Unexpected token with ascii_code ({}): {}", +currentChar, currentChar));

    std::string str;
    currentChar = readIf(str, isalpha);

    if (currentChar != ':')
        reportErrorAndExit(fmt::format("Expected token: ':', found: (ASCIICode: {}){}",
                                       +currentChar, currentChar));

    if (auto keyword = keywords.find(str); keyword != keywords.end()) {
        switch (keyword->second) {
            case Keywords::ChecksKeyword:
                parserState = ParserState::ParsingChecks;
                break;
            case Keywords::CheckConfigs:
                parserState = ParserState::ParsingCheckConfigs;
                break;
        }
    }
    else {
        reportErrorAndExit(fmt::format("Expected a keyword found: {}", str));
    }
}

void TidyConfigParser::parseChecks() {
    while (!fileStream.eof()) {
        TidyConfig::CheckStatus newCheckState = TidyConfig::CheckStatus::ENABLED;
        bool checkGroupParsed = false;
        bool ruleParsed = false;
        std::string checkGroup;
        std::string checkName;

        // Get the first char
        char currentChar = nextChar();

        // If it is a new line ignore it and get the following char
        while (currentChar == '\n')
            currentChar = nextChar();

        if (currentChar == '-')
            newCheckState = TidyConfig::CheckStatus::DISABLED;
        else if (isalpha(currentChar))
            checkGroup.push_back(currentChar);
        else if (currentChar == '*') {
            toggleAllChecks(TidyConfig::CheckStatus::ENABLED);
            currentChar = nextChar();
            if (currentChar == '\n' || currentChar == 0) {
                while (peekChar() == '\n')
                    nextChar();
                parserState = TidyConfigParser::ParserState::Initial;
                return;
            }
            else if (currentChar == ',') {
                currentChar = nextChar();
                if (currentChar != '\n') {
                    reportErrorAndExit(fmt::format("Expected new line but found: ({}){}",
                                                   +currentChar, currentChar));
                }
                continue;
            }
            else {
                reportErrorAndExit(
                    fmt::format("Expected ',' but found: ({}){}", +currentChar, currentChar));
            }
        }
        else {
            reportErrorAndExit(fmt::format("Expected '-' or '*' or a letter but found: ({}){}",
                                           +currentChar, currentChar));
        }

        // Parse second char
        currentChar = nextChar();

        if (currentChar == '*') {
            if (checkGroup.size())
                reportErrorAndExit("Unexpected '*'");
            ruleParsed = true;
            toggleAllChecks(TidyConfig::CheckStatus::DISABLED);
        }
        else if (currentChar == '-')
            checkGroupParsed = true;
        else if (isalpha(currentChar))
            checkGroup.push_back(currentChar);
        else {
            reportErrorAndExit(fmt::format("Expected '*' or a letter but found: ({}){}",
                                           +currentChar, currentChar));
        }

        if (ruleParsed) {
            currentChar = nextChar();
            if (currentChar == '\n' || currentChar == 0) {
                while (peekChar() == '\n')
                    nextChar();
                parserState = TidyConfigParser::ParserState::Initial;
                return;
            }
            else if (currentChar != ',') {
                reportErrorAndExit(
                    fmt::format("Expected ',' but found: ({}){}", +currentChar, currentChar));
            }
            continue;
        }

        // Parse group name
        while (!checkGroupParsed) {
            currentChar = nextChar();
            if (currentChar == '-')
                checkGroupParsed = true;
            else if (isalpha(currentChar))
                checkGroup.push_back(currentChar);
            else {
                reportErrorAndExit(fmt::format("Expected '-' or a letter but found: ({}){}",
                                               +currentChar, currentChar));
            }
        }

        // Parse check name
        bool checkParsed = false;
        while (true) {
            currentChar = nextChar();
            if (currentChar == ',') {
                toggleCheck(checkGroup, checkName, newCheckState);
                if (nextChar() != '\n') {
                    reportErrorAndExit(fmt::format("Expected new line but found: ({}){}",
                                                   +currentChar, currentChar));
                }
                break;
            }
            else if (currentChar == '*') {
                if (checkName.size())
                    reportErrorAndExit("Unexpected '*'");
                toggleAllGroupChecks(checkGroup, newCheckState);
                checkParsed = true;
            }
            else if (isalpha(currentChar) || currentChar == '-') {
                checkName.push_back(currentChar);
            }
            else if (currentChar == '\n' || currentChar == 0) {
                while (peekChar() == '\n')
                    nextChar();
                if (!checkParsed)
                    toggleCheck(checkGroup, checkName, newCheckState);
                parserState = ParserState::Initial;
                return;
            }
            else {
                reportErrorAndExit(fmt::format("Unexpected ({}){}", +currentChar, currentChar));
            }
        }
    }
}

void TidyConfigParser::parseCheckConfigs() {
    while (!fileStream.eof()) {
        // Parse optional newline
        if (peekChar() == '\n')
            nextChar();

        // Parse option name
        std::string optionName;
        char currentChar = readIf(optionName, isalpha);

        if (currentChar != ':') {
            reportErrorAndExit(fmt::format("Expected ':' or a letter but found ({}){}",
                                           +currentChar, currentChar));
        }

        // Parse multiple option values
        std::vector<std::string> optionValues;

        auto isRegexMeta = [](char c) {
            return c == '.' || c == '^' || c == '$' || c == '*' || c == '+' || c == '?' ||
                   c == '{' || c == '}' || c == '[' || c == ']' || c == '\\' || c == '|' ||
                   c == '(' || c == ')';
        };

        auto isOptionValueChar = [](char c) { return isalnum(c) || c == '_'; };
        auto isRegexOptionValueChar = [&](char c) {
            return isalnum(c) || isRegexMeta(c) || c == '_';
        };

        if (peekChar() == '[') {
            currentChar = nextChar(); // skip '['

            do {
                std::string optionValue;
                currentChar = readIf(optionValue, isOptionValueChar);
                if (!optionValue.empty())
                    optionValues.emplace_back(optionValue);
            } while (currentChar == ',');

            if (currentChar != ']') {
                reportErrorAndExit(
                    fmt::format("Expected ']' but found ({}){}", +currentChar, currentChar));
            }
            currentChar = nextChar();
        }
        else if (peekChar() == '"') {
            currentChar = nextChar(); // skip '"'

            std::string optionValue;
            currentChar = readIf(optionValue, isRegexOptionValueChar);
            if (!optionValue.empty())
                optionValues.emplace_back((optionValue));

            if (currentChar != '"') {
                reportErrorAndExit(
                    fmt::format("Expected '\"' but found ({}){}", +currentChar, currentChar));
            }
            currentChar = nextChar();
        }
        else { // Parse single option value
            std::string optionValue;
            currentChar = readIf(optionValue, isOptionValueChar);
            optionValues.emplace_back(optionValue);
        }

        if (currentChar == ',') {
            setCheckConfig(optionName, optionValues);
            if (nextChar() != '\n') {
                reportErrorAndExit(
                    fmt::format("Expected new line but found: ({}){}", +currentChar, currentChar));
            }
        }
        else if (currentChar == '\n' || currentChar == 0) {
            while (peekChar() == '\n')
                nextChar();
            setCheckConfig(optionName, optionValues);
            parserState = ParserState::Initial;
            return;
        }
        else {
            reportErrorAndExit(fmt::format("Expected ',' new line or a letter but found ({}){}",
                                           +currentChar, currentChar));
        }
    }
}

void TidyConfigParser::toggleAllChecks(TidyConfig::CheckStatus status) {
    config.toggleAl(status);
}

void TidyConfigParser::toggleAllGroupChecks(const std::string& groupName,
                                            TidyConfig::CheckStatus status) {
    auto kind = slang::tidyKindFromStr(groupName);
    if (!kind)
        reportErrorAndExit(fmt::format("Group {} does not exist", groupName));

    config.toggleGroup(kind.value(), status);
}

void TidyConfigParser::toggleCheck(const std::string& groupName, const std::string& checkName,
                                   TidyConfig::CheckStatus status) {
    if (checkName.empty()) {
        reportWarning(fmt::format(
            "Empty check name in group {0}, you can toggle the whole group with {0}-*", groupName));
        return;
    }

    auto kind = slang::tidyKindFromStr(groupName);
    if (!kind)
        reportErrorAndExit(fmt::format("Group {} does not exist", groupName));
    bool found = config.toggleCheck(kind.value(), formatCheckName(checkName), status);

    if (!found)
        reportWarning(
            fmt::format("Check name {} does not exist in group {}", checkName, groupName));
}

void TidyConfigParser::parseConfigValue(std::string& config, std::string&& configValue) {
    config = std::move(configValue);
}

void TidyConfigParser::parseConfigValue(bool& config, std::string&& configValue) {
    std::transform(configValue.begin(), configValue.end(), configValue.begin(), ::tolower);
    if (configValue == "true" || configValue == "false") {
        config = configValue == "true";
    }
    else if (configValue == "1" || configValue == "0") {
        config = configValue == "1";
    }
    else {
        reportErrorAndExit(fmt::format("Expected boolean expression but got '{}'", configValue));
    }
}

void TidyConfigParser::setCheckConfig(const std::string& configName,
                                      std::vector<std::string> configValues) {
    SLANG_TRY {
        config.visitConfig(configName, [&](auto& v) {
            if constexpr (is_vector_v<std::remove_cvref_t<decltype(v)>>) {
                parseConfigValue(v, std::move(configValues));
            }
            else {
                if (configValues.size() != 1) {
                    reportErrorAndExit(
                        fmt::format("Expected one configuration value for '{}' but got {}",
                                    configName, configValues.size()));
                }
                parseConfigValue(v, std::move(configValues.front()));
            }
        });
    }
    SLANG_CATCH(std::invalid_argument & exception) {
#if __cpp_exceptions
        reportWarning(exception.what());
#endif
    }
}

void TidyConfigParser::reportErrorAndExit(const std::string& str) const {
    slang::OS::printE(fmt::format("Error while parsing slang-tidy config: {} "
                                  "{}:{}\n\t{}\n",
                                  filePath, line, col, str));
    exit(1);
}

void TidyConfigParser::reportWarning(const std::string& str) const {
    slang::OS::print(fmt::format("Warning while parsing slang-tidy config: {} "
                                 "{}:{}\n\t{}\n",
                                 filePath, line, col, str));
}

std::string TidyConfigParser::formatCheckName(const std::string& checkName) {
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
