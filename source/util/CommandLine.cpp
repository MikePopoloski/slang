//------------------------------------------------------------------------------
// CommandLine.cpp
// Command line argument parsing support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/CommandLine.h"

#include <charconv>
#include <cstdlib>
#include <filesystem>
#include <fmt/core.h>

#include "slang/text/CharInfo.h"
#include "slang/util/OS.h"
#include "slang/util/SmallVector.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang {

void CommandLine::add(string_view name, std::optional<bool>& value, string_view desc) {
    addInternal(name, &value, desc, {});
}

void CommandLine::add(string_view name, std::optional<int32_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::optional<uint32_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::optional<int64_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::optional<uint64_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::optional<double>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::optional<std::string>& value, string_view desc,
                      string_view valueName, bool isFileName) {
    addInternal(name, &value, desc, valueName, isFileName);
}

void CommandLine::add(string_view name, std::vector<int32_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::vector<uint32_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::vector<int64_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::vector<uint64_t>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::vector<double>& value, string_view desc,
                      string_view valueName) {
    addInternal(name, &value, desc, valueName);
}

void CommandLine::add(string_view name, std::vector<std::string>& value, string_view desc,
                      string_view valueName, bool isFileName) {
    addInternal(name, &value, desc, valueName, isFileName);
}

void CommandLine::add(string_view name, OptionCallback cb, string_view desc, string_view valueName,
                      bool isFileName) {
    addInternal(name, cb, desc, valueName, isFileName);
}

void CommandLine::addInternal(string_view name, OptionStorage storage, string_view desc,
                              string_view valueName, bool isFileName) {
    if (name.empty())
        throw std::invalid_argument("Name cannot be empty");

    auto option = std::make_shared<Option>();
    option->desc = desc;
    option->valueName = valueName;
    option->allArgNames = name;
    option->storage = std::move(storage); // NOLINT
    option->isFileName = isFileName;

    while (true) {
        size_t index = name.find_first_of(',');
        string_view curr = name;
        if (index != string_view::npos)
            curr = name.substr(0, index);

        if (curr.length() <= 1 || (curr[0] != '-' && curr[0] != '+'))
            throw std::invalid_argument("Names must begin with '-', '+', or '--'");

        if (curr[0] != '+') {
            curr = curr.substr(1);
            if (curr[0] == '-') {
                curr = curr.substr(1);
                if (curr.empty())
                    throw std::invalid_argument("Names must begin with '-' or '--'");
            }
            else if (curr.length() > 1) {
                throw std::invalid_argument("Long name requires '--' prefix");
            }
        }

        if (!optionMap.try_emplace(std::string(curr), option).second) {
            throw std::invalid_argument(
                fmt::format("Argument with name '{}' already exists", curr));
        }

        if (index == string_view::npos)
            break;
        name = name.substr(index + 1);
    }

    orderedOptions.emplace_back(option);
}

void CommandLine::setPositional(std::vector<std::string>& values, string_view valueName,
                                bool isFileName) {
    if (positional)
        throw std::runtime_error("Can only set one positional argument");

    positional = std::make_shared<Option>();
    positional->valueName = valueName;
    positional->storage = &values;
    positional->isFileName = isFileName;
}

void CommandLine::setPositional(OptionCallback cb, string_view valueName, bool isFileName) {
    if (positional)
        throw std::runtime_error("Can only set one positional argument");

    positional = std::make_shared<Option>();
    positional->valueName = valueName;
    positional->storage = cb;
    positional->isFileName = isFileName;
}

bool CommandLine::parse(int argc, const char* const argv[]) {
    SmallVector<string_view, 8> args{size_t(argc), UninitializedTag()};
    for (int i = 0; i < argc; i++)
        args.push_back(argv[i]);

    return parse(args);
}

#if defined(_MSC_VER)

bool CommandLine::parse(int argc, const wchar_t* const argv[]) {
    SmallVector<std::string, 8> storage{size_t(argc), UninitializedTag()};
    SmallVector<string_view, 8> args{size_t(argc), UninitializedTag()};
    for (int i = 0; i < argc; i++) {
        storage.push_back(narrow(argv[i]));
        args.push_back(storage.back());
    }

    return parse(args);
}

#endif

bool CommandLine::parse(string_view argList, ParseOptions options) {
    bool hasArg = false;
    std::string current;
    SmallVector<std::string, 8> storage;

    parseStr(argList, options, hasArg, current, storage);

    if (hasArg)
        storage.emplace_back(std::move(current));

    SmallVector<string_view, 8> args(storage.size(), UninitializedTag());
    for (auto& arg : storage)
        args.push_back(arg);

    return parse(args, options);
}

void CommandLine::parseStr(string_view argList, ParseOptions options, bool& hasArg,
                           std::string& current, SmallVectorBase<std::string>& storage) {
    auto pushArg = [&]() {
        if (hasArg) {
            storage.emplace_back(std::move(current));
            current.clear();
            hasArg = false;
        }
    };

    auto ptr = argList.data();
    auto end = ptr + argList.size();
    while (ptr != end) {
        // Whitespace breaks up arguments.
        char c = *ptr++;
        if (isWhitespace(c)) {
            pushArg();
            continue;
        }

        // Check for and consume comments.
        if (options.supportComments && (c == '#' || c == '/')) {
            // Slash character only applies if we aren't building an argument already.
            // The hash always applies, even if adjacent to an argument.
            if (c == '#') {
                pushArg();
                while (ptr != end && !isNewline(*ptr))
                    ptr++;
                continue;
            }

            if (!hasArg && ptr != end) {
                if (*ptr == '/') {
                    pushArg();
                    ptr++;
                    while (ptr != end && !isNewline(*ptr))
                        ptr++;
                    continue;
                }
                else if (*ptr == '*') {
                    pushArg();
                    ptr++;
                    while (ptr != end) {
                        c = *ptr++;
                        if (c == '*' && ptr != end && *ptr == '/') {
                            ptr++;
                            break;
                        }
                    }
                    continue;
                }
            }
        }

        // Look for environment variables to expand.
        if (c == '$' && options.expandEnvVars && ptr != end) {
            std::string result = expandVar(ptr, end);

            ParseOptions newOptions = options;
            newOptions.expandEnvVars = false;
            parseStr(result, newOptions, hasArg, current, storage);
            continue;
        }

        // Any non-whitespace character here means we are building an argument.
        hasArg = true;

        // Escape character preserves the value of the next character.
        if (c == '\\') {
            if (ptr != end)
                current += *ptr++;
            continue;
        }

        // Single quotes consume all characters until the next single quote.
        if (c == '\'') {
            while (ptr != end) {
                c = *ptr++;
                if (c == '\'')
                    break;
                current += c;
            }
            continue;
        }

        // Double quotes consume all characters except escaped characters.
        if (c == '"') {
            while (ptr != end) {
                c = *ptr++;
                if (c == '"')
                    break;

                // Only backslashes and quotes can be escaped.
                if (c == '\\' && ptr != end && (*ptr == '\\' || *ptr == '"'))
                    c = *ptr++;

                if (c == '$' && options.expandEnvVars && ptr != end)
                    current.append(expandVar(ptr, end));
                else
                    current += c;
            }
            continue;
        }

        // Otherwise we just have a normal character.
        current += c;
    }
}

std::string CommandLine::expandVar(const char*& ptr, const char* end) {
    // Three forms for environment variables to try:
    // $VAR
    // $(VAR)
    // ${VAR}
    char c = *ptr++;
    if (c == '(' || c == '{') {
        char startDelim = c;
        char endDelim = c == '(' ? ')' : '}';
        std::string varName;
        while (ptr != end) {
            c = *ptr++;
            if (c == endDelim)
                return OS::getEnv(varName);

            varName += c;
        }

        // If we reach the end, we didn't find a closing delimiter.
        // Don't try to expand, just return the whole thing we collected.
        return "$"s + startDelim + varName;
    }
    else if (isValidCIdChar(c)) {
        std::string varName;
        varName += c;
        while (ptr != end && isValidCIdChar(*ptr))
            varName += *ptr++;

        return OS::getEnv(varName);
    }
    else {
        // This is not a possible variable name so just return what we have.
        return "$"s + c;
    }
}

bool CommandLine::parse(span<const string_view> args, ParseOptions options) {
    if (optionMap.empty())
        throw std::runtime_error("No options defined");

    if (!options.ignoreProgramName) {
        if (args.empty())
            throw std::runtime_error("Expected at least one argument");

        programName = fs::path(fs::u8path(args[0])).filename().u8string();
        args = args.subspan(1);
    }

    Option* expectingVal = nullptr;
    string_view expectingValName;
    bool doubleDash = false;
    bool hadUnknowns = false;
    string_view firstPositional;

    int skip = 0;
    for (auto arg : args) {
        // Skip N arguments if needed (set by the cmdIgnore feature)
        if (skip) {
            skip--;
            continue;
        }

        // If we were previously expecting a value, set that now.
        if (expectingVal) {
            std::string result = expectingVal->set(expectingValName, arg, options.ignoreDuplicates);
            if (!result.empty())
                errors.emplace_back(fmt::format("{}: {}", programName, result));

            expectingVal = nullptr;
            continue;
        }

        // This is a positional argument if:
        // - Doesn't start with '-' and '+'
        // - Is exactly '-'
        // - Or we've seen a double dash already
        if (arg.length() <= 1 || doubleDash || (arg[0] != '-' && arg[0] != '+')) {
            if (firstPositional.empty())
                firstPositional = arg;

            if (positional)
                positional->set(""sv, arg, options.ignoreDuplicates);

            continue;
        }

        // Double dash indicates that all further arguments are positional.
        if (arg == "--"sv) {
            doubleDash = true;
            continue;
        }

        // Check if arg is in the list of commands to skip.
        if (!cmdIgnore.empty()) {
            // If we ignore a vendor command of the form +xx ,
            // we match on any +xx+yyy command as +yy is the command's argument.
            string_view ignoreArg = arg;
            if (arg[0] == '+') {
                size_t plusIndex = arg.substr(1).find_first_of('+');
                if (plusIndex != string_view::npos) {
                    ignoreArg = arg.substr(0, plusIndex +
                                                  1); // +1 because we started from arg.substr(1)
                }
            }

            if (auto it = cmdIgnore.find(std::string(ignoreArg)); it != cmdIgnore.end()) {
                // if yes, find how many args to skip
                skip = it->second;
                continue;
            }
        }

        // Check if arg is in the list of commands to translate.
        if (!cmdRename.empty()) {
            if (auto it = cmdRename.find(std::string(arg)); it != cmdRename.end()) {
                // if yes, rename argument
                arg = it->second;
            }
        }

        // Handle plus args, which are treated differently from all others.
        if (arg[0] == '+') {
            handlePlusArg(arg, options, hadUnknowns);
            continue;
        }

        // Get the raw name without leading dashes.
        bool longName = false;
        string_view name = arg.substr(1);
        if (name[0] == '-') {
            longName = true;
            name = name.substr(1);
        }

        string_view value;
        auto option = findOption(name, value);

        // If we didn't find the option and there was only a single dash,
        // maybe this was actually a group of single-char options or a prefixed value.
        if (!option && !longName) {
            option = tryGroupOrPrefix(name, value, options);
            if (option)
                arg = name;
        }

        // If we still didn't find it, that's an error.
        if (!option) {
            // Try to find something close to give a better error message.
            auto error = fmt::format("{}: unknown command line argument '{}'"sv, programName, arg);
            auto nearest = findNearestMatch(arg);
            if (!nearest.empty())
                error += fmt::format(", did you mean '{}'?"sv, nearest);

            hadUnknowns = true;
            errors.emplace_back(std::move(error));
            continue;
        }

        // Otherwise, we found what we wanted. If we have a value already, go ahead
        // and set it. Otherwise if we're expecting a value, assume that it will come
        // in the next argument.
        if (value.empty() && option->expectsValue()) {
            expectingVal = option;
            expectingValName = arg;
        }
        else {
            std::string result = option->set(arg, value, options.ignoreDuplicates);
            if (!result.empty())
                errors.emplace_back(fmt::format("{}: {}", programName, result));
        }
    }

    if (expectingVal) {
        errors.emplace_back(fmt::format("{}: no value provided for argument '{}'"sv, programName,
                                        expectingValName));
    }

    if (!positional && !firstPositional.empty() && !hadUnknowns) {
        errors.emplace_back(
            fmt::format("{}: positional arguments are not allowed (see e.g. '{}')"sv, programName,
                        firstPositional));
    }

    return errors.empty();
}

std::string CommandLine::getHelpText(string_view overview) const {
    std::string result;
    if (!overview.empty())
        result = fmt::format("OVERVIEW: {}\n\n"sv, overview);

    result += fmt::format("USAGE: {} [options]"sv, programName);
    if (positional)
        result += fmt::format(" {}...", positional->valueName);

    result += "\n\nOPTIONS:\n"sv;

    // For each option group that takes a value, tack on the value name.
    // Then compute the maximum length of any particular group's key.
    size_t maxLen = 0;
    std::vector<std::pair<Option*, std::string>> lines;
    for (auto& opt : orderedOptions) {
        std::string key = opt->allArgNames;
        std::string& val = opt->valueName;
        if (!val.empty()) {
            if (val[0] != '=')
                key += ' ';
            key += val;
        }

        maxLen = std::max(maxLen, key.length());
        lines.emplace_back(opt.get(), std::move(key));
    }

    // Add two spaces so that the description text is offset from the longest option name.
    maxLen += 2;

    // Finally append all groups to the output.
    std::string indent = fmt::format("  {:{}}"sv, " "sv, maxLen);
    for (auto& [opt, key] : lines) {
        result += fmt::format("  {:{}}"sv, key, maxLen);
        if (!opt->desc.empty()) {
            string_view desc = opt->desc;
            while (true) {
                size_t index = desc.find_first_of('\n');
                if (index == string_view::npos) {
                    result += desc;
                    break;
                }

                result += desc.substr(0, index + 1);
                result += indent;
                desc = desc.substr(index + 1);
            }
        }
        result += "\n";
    }

    return result;
}

void CommandLine::handlePlusArg(string_view arg, ParseOptions options, bool& hadUnknowns) {
    // Values are plus separated.
    string_view value;
    size_t idx = arg.find_first_of('+', 2);
    if (idx != string_view::npos) {
        value = arg.substr(idx + 1);
        arg = arg.substr(0, idx);
    }

    // TODO: change once we have heterogeneous lookup from C++20
    auto it = optionMap.find(std::string(arg));
    if (it == optionMap.end()) {
        hadUnknowns = true;
        errors.emplace_back(
            fmt::format("{}: unknown command line argument '{}'"sv, programName, arg));
        return;
    }

    auto option = it->second.get();
    if (value.empty()) {
        if (option->expectsValue()) {
            errors.emplace_back(
                fmt::format("{}: no value provided for argument '{}'"sv, programName, arg));
        }
        else {
            std::string result = option->set(arg, value, options.ignoreDuplicates);
            ASSERT(result.empty());
        }
        return;
    }

    do {
        string_view curr = value;
        idx = value.find_first_of('+');
        if (idx != string_view::npos) {
            value = value.substr(idx + 1);
            curr = curr.substr(0, idx);
        }
        else {
            value = {};
        }

        std::string result = option->set(arg, curr, options.ignoreDuplicates);
        if (!result.empty())
            errors.emplace_back(fmt::format("{}: {}", programName, result));

    } while (!value.empty());
}

CommandLine::Option* CommandLine::findOption(string_view arg, string_view& value) const {
    // If there is an equals sign, strip off the value.
    size_t equalsIndex = arg.find_first_of('=');
    if (equalsIndex != string_view::npos) {
        value = arg.substr(equalsIndex + 1);
        arg = arg.substr(0, equalsIndex);
    }

    // TODO: change once we have heterogeneous lookup from C++20
    auto it = optionMap.find(std::string(arg));
    if (it == optionMap.end())
        return nullptr;

    return it->second.get();
}

CommandLine::Option* CommandLine::tryGroupOrPrefix(string_view& arg, string_view& value,
                                                   ParseOptions options) {
    // This function handles cases like:
    // -abcvalue
    // Where -a, -b, and -c are arguments and value is the value for argument -c
    while (true) {
        auto name = arg.substr(0, 1);
        auto option = findOption(name, value);
        if (!option)
            return nullptr;

        // If a value is expected, treat the rest of the argument as the value.
        value = arg.substr(1);
        if (option->expectsValue() || value.empty()) {
            if (!value.empty() && value[0] == '=')
                value = value.substr(1);
            return option;
        }

        // Otherwise this is a single flag and we should move on.
        option->set(name, ""sv, options.ignoreDuplicates);
        arg = value;
    }
}

std::string CommandLine::findNearestMatch(string_view arg) const {
    if (arg.length() <= 2)
        return {};

    size_t equalsIndex = arg.find_first_of('=');
    if (equalsIndex != string_view::npos)
        arg = arg.substr(0, equalsIndex);

    string_view bestName;
    int bestDistance = 5;

    for (auto& [key, value] : optionMap) {
        if (key[0] == '+')
            continue;

        int dist = editDistance(key, arg, /* allowReplacements */ true, bestDistance);
        if (dist < bestDistance) {
            bestName = key;
            bestDistance = dist;
        }
    }

    if (bestName.empty())
        return {};

    if (bestName.length() == 1)
        return "-"s + std::string(bestName);

    return "--"s + std::string(bestName);
}

bool CommandLine::Option::expectsValue() const {
    return storage.index() != 0;
}

std::string CommandLine::Option::set(string_view name, string_view value, bool ignoreDup) {
    std::string pathMem;
    if (isFileName && !value.empty()) {
        std::error_code ec;
        fs::path path = fs::weakly_canonical(fs::u8path(value), ec);
        if (!ec) {
            pathMem = path.u8string();
            value = pathMem;
        }
    }

    return std::visit(
        [&](auto&& arg) {
            if constexpr (std::is_same_v<OptionCallback, std::decay_t<decltype(arg)>>) {
                return set(arg, name, value);
            }
            else {
                if (!allowValue(*arg)) {
                    if (ignoreDup)
                        return std::string();
                    return fmt::format("more than one value provided for argument '{}'"sv, name);
                }
                return set(*arg, name, value);
            }
        },
        storage);
}

static std::optional<bool> parseBool(string_view name, string_view value, std::string& error) {
    if (value.empty())
        return true;
    if (value == "True" || value == "true")
        return true;
    if (value == "False" || value == "false")
        return false;

    error = fmt::format("invalid value '{}' for boolean argument '{}'", value, name);
    return {};
}

template<typename T>
static std::optional<T> parseInt(string_view name, string_view value, std::string& error) {
    if (value.empty()) {
        error = fmt::format("expected value for argument '{}'", name);
        return {};
    }

    T val;
    auto end = value.data() + value.size();
    auto result = std::from_chars(value.data(), end, val);
    if (result.ec != std::errc() || result.ptr != end) {
        error = fmt::format("invalid value '{}' for integer argument '{}'", value, name);
        return {};
    }

    return val;
}

static std::optional<double> parseDouble(string_view name, string_view value, std::string& error) {
    if (value.empty()) {
        error = fmt::format("expected value for argument '{}'", name);
        return {};
    }

    size_t pos;
    std::optional<double> val = strToDouble(value, &pos);
    if (!val || pos != value.size())
        error = fmt::format("invalid value '{}' for float argument '{}'", value, name);

    return val;
}

std::string CommandLine::Option::set(std::optional<bool>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseBool(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<int32_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseInt<int32_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<uint32_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseInt<uint32_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<int64_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseInt<int64_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<uint64_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseInt<uint64_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<double>& target, string_view name,
                                     string_view value) {
    std::string error;
    target = parseDouble(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<std::string>& target, string_view,
                                     string_view value) {
    target = value;
    return {};
}

std::string CommandLine::Option::set(std::vector<int32_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    auto result = parseInt<int32_t>(name, value, error);
    if (result)
        target.push_back(*result);
    return error;
}

std::string CommandLine::Option::set(std::vector<uint32_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    auto result = parseInt<uint32_t>(name, value, error);
    if (result)
        target.push_back(*result);
    return error;
}

std::string CommandLine::Option::set(std::vector<int64_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    auto result = parseInt<int64_t>(name, value, error);
    if (result)
        target.push_back(*result);
    return error;
}

std::string CommandLine::Option::set(std::vector<uint64_t>& target, string_view name,
                                     string_view value) {
    std::string error;
    auto result = parseInt<uint64_t>(name, value, error);
    if (result)
        target.push_back(*result);
    return error;
}

std::string CommandLine::Option::set(std::vector<double>& target, string_view name,
                                     string_view value) {
    std::string error;
    auto result = parseDouble(name, value, error);
    if (result)
        target.push_back(*result);
    return error;
}

std::string CommandLine::Option::set(std::vector<std::string>& target, string_view,
                                     string_view value) {
    target.emplace_back(value);
    return {};
}

std::string CommandLine::Option::set(OptionCallback& target, string_view, string_view value) {
    return target(value);
}

std::string CommandLine::addIgnoreCommand(string_view value) {
    const size_t firstCommaIndex = value.find_first_of(',');
    const size_t lastCommaIndex = value.find_last_of(',');
    if (firstCommaIndex == string_view::npos || firstCommaIndex != lastCommaIndex)
        return fmt::format("missing or extra comma in argument '{}'", value);

    const string_view numArgs = value.substr(firstCommaIndex + 1);
    value = value.substr(0, firstCommaIndex);

    std::string error;
    auto result = parseInt<int>("", numArgs, error);
    if (result) {
        cmdIgnore[std::string(value)] = *result;
        return {};
    }
    return error;
}

std::string CommandLine::addRenameCommand(string_view value) {
    const size_t firstCommaIndex = value.find_first_of(',');
    const size_t lastCommaIndex = value.find_last_of(',');
    if (firstCommaIndex == string_view::npos || firstCommaIndex != lastCommaIndex)
        return fmt::format("missing or extra comma in argument '{}'", value);

    const string_view slangName = value.substr(firstCommaIndex + 1);
    value = value.substr(0, firstCommaIndex);
    cmdRename[std::string(value)] = slangName;
    return {};
}

} // namespace slang
