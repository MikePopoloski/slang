//------------------------------------------------------------------------------
// CommandLine.cpp
// Command line argument parsing support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/CommandLine.h"

#include <charconv>
#include <filesystem>
#include <fmt/core.h>

#include "slang/text/CharInfo.h"
#include "slang/util/OS.h"
#include "slang/util/SmallVector.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang {

void CommandLine::add(std::string_view name, std::optional<bool>& value, std::string_view desc,
                      bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, {}, flags);
}

void CommandLine::add(std::string_view name, std::optional<int32_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::optional<uint32_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::optional<int64_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::optional<uint64_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::optional<double>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::optional<std::string>& value,
                      std::string_view desc, std::string_view valueName,
                      bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<int32_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<uint32_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<int64_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<uint64_t>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<double>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, std::vector<std::string>& value, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, &value, desc, valueName, flags);
}

void CommandLine::add(std::string_view name, OptionCallback cb, std::string_view desc,
                      std::string_view valueName, bitmask<CommandLineFlags> flags) {
    addInternal(name, cb, desc, valueName, flags);
}

void CommandLine::addInternal(std::string_view name, OptionStorage storage, std::string_view desc,
                              std::string_view valueName, bitmask<CommandLineFlags> flags) {
    if (name.empty())
        SLANG_THROW(std::invalid_argument("Name cannot be empty"));

    auto option = std::make_shared<Option>();
    option->desc = desc;
    option->valueName = valueName;
    option->allArgNames = name;
    option->storage = std::move(storage); // NOLINT
    option->flags = flags;

    while (true) {
        size_t index = name.find_first_of(',');
        std::string_view curr = name;
        if (index != std::string_view::npos)
            curr = name.substr(0, index);

        if (curr.length() <= 1 || (curr[0] != '-' && curr[0] != '+'))
            SLANG_THROW(std::invalid_argument("Names must begin with '-', '+', or '--'"));

        if (curr[0] != '+') {
            curr = curr.substr(1);
            if (curr[0] == '-') {
                curr = curr.substr(1);
                if (curr.empty())
                    SLANG_THROW(std::invalid_argument("Names must begin with '-' or '--'"));
            }
            else if (curr.length() > 1) {
                SLANG_THROW(std::invalid_argument("Long name requires '--' prefix"));
            }
        }

        if (!optionMap.try_emplace(std::string(curr), option).second) {
            SLANG_THROW(
                std::invalid_argument(fmt::format("Argument with name '{}' already exists", curr)));
        }

        if (index == std::string_view::npos)
            break;
        name = name.substr(index + 1);
    }

    orderedOptions.emplace_back(option);
}

void CommandLine::setPositional(std::vector<std::string>& values, std::string_view valueName,
                                bitmask<CommandLineFlags> flags) {
    if (positional)
        SLANG_THROW(std::runtime_error("Can only set one positional argument"));

    positional = std::make_shared<Option>();
    positional->valueName = valueName;
    positional->storage = &values;
    positional->flags = flags;
}

void CommandLine::setPositional(const OptionCallback& cb, std::string_view valueName,
                                bitmask<CommandLineFlags> flags) {
    if (positional)
        SLANG_THROW(std::runtime_error("Can only set one positional argument"));

    positional = std::make_shared<Option>();
    positional->valueName = valueName;
    positional->storage = cb;
    positional->flags = flags;
}

bool CommandLine::parse(int argc, const char* const argv[]) {
    SmallVector<std::string_view, 8> args{size_t(argc), UninitializedTag()};
    for (int i = 0; i < argc; i++)
        args.push_back(argv[i]);

    return parse(args);
}

bool CommandLine::parse(std::string_view argList, ParseOptions options) {
    bool hasArg = false;
    std::string current;
    SmallVector<std::string, 8> storage;

    parseStr(argList, options, hasArg, current, storage);

    if (hasArg)
        storage.emplace_back(std::move(current));

    SmallVector<std::string_view, 8> args(storage.size(), UninitializedTag());
    for (auto& arg : storage)
        args.push_back(arg);

    return parse(args, options);
}

void CommandLine::parseStr(std::string_view argList, ParseOptions options, bool& hasArg,
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
            std::string result = OS::parseEnvVar(ptr, end);

            ParseOptions newOptions = options;
            newOptions.expandEnvVars = false;
            parseStr(result, newOptions, hasArg, current, storage);
            continue;
        }

        // Escape character preserves the value of the next character.
        if (c == '\\') {
            if (ptr != end && *ptr != '\n' && *ptr != '\r') {
                current += *ptr++;
                hasArg = true;
            }
            continue;
        }

        // Any non-whitespace character here means we are building an argument.
        hasArg = true;

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
                    current.append(OS::parseEnvVar(ptr, end));
                else
                    current += c;
            }
            continue;
        }

        // Otherwise we just have a normal character.
        current += c;
    }
}

bool CommandLine::parse(std::span<const std::string_view> args, ParseOptions options) {
    if (optionMap.empty())
        SLANG_THROW(std::runtime_error("No options defined"));

    if (!options.ignoreProgramName) {
        if (args.empty())
            SLANG_THROW(std::runtime_error("Expected at least one argument"));

        programName = getU8Str(fs::path(args[0]).filename());
        args = args.subspan(1);
    }

    Option* expectingVal = nullptr;
    std::string expectingValName;
    bool doubleDash = false;
    bool hadUnknowns = false;
    std::string_view firstPositional;

    int skip = 0;
    for (auto arg : args) {
        // Skip N arguments if needed (set by the cmdIgnore feature).
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

        // Check if arg is in the list of commands to skip or translate.
        if (!cmdIgnore.empty() || !cmdRename.empty()) {
            std::string_view ignoreArg = arg;
            std::string_view remainder;
            if (arg[0] == '+') {
                // If we ignore a vendor command of the form +xx ,
                // we match on any +xx+yyy command as +yy is the command's argument.
                size_t plusIndex = arg.find_first_of('+', 1);
                if (plusIndex != std::string_view::npos) {
                    ignoreArg = arg.substr(0, plusIndex);
                    remainder = arg.substr(plusIndex);
                }
            }
            else {
                // Otherwise we look up to the first equals for the name to ignore.
                size_t equalsIndex = arg.find_first_of('=');
                if (equalsIndex != std::string_view::npos) {
                    ignoreArg = arg.substr(0, equalsIndex);
                    remainder = arg.substr(equalsIndex);
                }
            }

            auto lookupStr = std::string(ignoreArg);
            if (auto it = cmdIgnore.find(lookupStr); it != cmdIgnore.end()) {
                // If yes, find how many args to skip.
                skip = it->second;
                continue;
            }

            if (auto it = cmdRename.find(lookupStr); it != cmdRename.end()) {
                // If yes, rename argument.
                auto renamed = it->second + std::string(remainder);
                handleArg(renamed, expectingVal, expectingValName, hadUnknowns, options);
                continue;
            }
        }

        // Otherwise just handle the argument.
        handleArg(arg, expectingVal, expectingValName, hadUnknowns, options);
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

void CommandLine::handleArg(std::string_view arg, Option*& expectingVal,
                            std::string& expectingValName, bool& hadUnknowns,
                            ParseOptions options) {
    // Handle plus args, which are treated differently from all others.
    if (arg[0] == '+') {
        handlePlusArg(arg, options, hadUnknowns);
        return;
    }

    // Get the raw name without leading dashes.
    bool longName = false;
    std::string_view name = arg.substr(1);
    if (name[0] == '-') {
        longName = true;
        name = name.substr(1);
    }

    std::string_view value;
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
        return;
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

std::string CommandLine::getHelpText(std::string_view overview) const {
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
            std::string_view desc = opt->desc;
            while (true) {
                size_t index = desc.find_first_of('\n');
                if (index == std::string_view::npos) {
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

void CommandLine::handlePlusArg(std::string_view arg, ParseOptions options, bool& hadUnknowns) {
    // Values are plus separated.
    std::string_view value;
    size_t idx = arg.find_first_of('+', 2);
    if (idx != std::string_view::npos) {
        value = arg.substr(idx + 1);
        arg = arg.substr(0, idx);
    }

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
            SLANG_ASSERT(result.empty());
        }
        return;
    }

    do {
        std::string_view curr = value;
        idx = value.find_first_of('+');
        if (idx != std::string_view::npos) {
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

CommandLine::Option* CommandLine::findOption(std::string_view arg, std::string_view& value) const {
    // If there is an equals sign, strip off the value.
    size_t equalsIndex = arg.find_first_of('=');
    if (equalsIndex != std::string_view::npos) {
        value = arg.substr(equalsIndex + 1);
        arg = arg.substr(0, equalsIndex);
    }

    auto it = optionMap.find(std::string(arg));
    if (it == optionMap.end())
        return nullptr;

    return it->second.get();
}

CommandLine::Option* CommandLine::tryGroupOrPrefix(std::string_view& arg, std::string_view& value,
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

std::string CommandLine::findNearestMatch(std::string_view arg) const {
    if (arg.length() <= 2)
        return {};

    size_t equalsIndex = arg.find_first_of('=');
    if (equalsIndex != std::string_view::npos)
        arg = arg.substr(0, equalsIndex);

    std::string_view bestName;
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

std::string CommandLine::Option::set(std::string_view name, std::string_view value,
                                     bool ignoreDup) {
    std::string pathMem;
    if (flags.has(CommandLineFlags::FilePath) && !value.empty() && value != "-") {
        std::error_code ec;
        fs::path path = fs::weakly_canonical(value, ec);
        if (!ec) {
            pathMem = getU8Str(path);
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

static std::optional<bool> parseBool(std::string_view name, std::string_view value,
                                     std::string& error) {
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
static std::optional<T> parseInt(std::string_view name, std::string_view value,
                                 std::string& error) {
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

static std::optional<double> parseDouble(std::string_view name, std::string_view value,
                                         std::string& error) {
    if (value.empty()) {
        error = fmt::format("expected value for argument '{}'", name);
        return {};
    }

    size_t pos;
    std::optional<double> val = strToDouble(value, &pos);
    if (!val || pos != value.size()) {
        error = fmt::format("invalid value '{}' for float argument '{}'", value, name);
        return {};
    }

    return val;
}

std::string CommandLine::Option::set(std::optional<bool>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseBool(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<int32_t>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseInt<int32_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<uint32_t>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseInt<uint32_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<int64_t>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseInt<int64_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<uint64_t>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseInt<uint64_t>(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<double>& target, std::string_view name,
                                     std::string_view value) {
    std::string error;
    target = parseDouble(name, value, error);
    return error;
}

std::string CommandLine::Option::set(std::optional<std::string>& target, std::string_view,
                                     std::string_view value) {
    target = value;
    return {};
}

static std::span<const std::string_view> parseList(std::string_view value, bool allowCommaList,
                                                   SmallVector<std::string_view>& splitMem) {
    if (allowCommaList) {
        while (true) {
            auto index = value.find_first_of(',');
            if (index == std::string_view::npos)
                break;

            splitMem.push_back(value.substr(0, index));
            value = value.substr(index + 1);
        }
    }
    splitMem.push_back(value);
    return splitMem;
}

template<typename T>
static std::string setIntList(std::vector<T>& target, std::string_view name, std::string_view value,
                              bitmask<CommandLineFlags> flags) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        std::string error;
        auto result = parseInt<T>(name, entry, error);
        if (!result)
            return error;

        target.push_back(*result);
    }
    return {};
}

std::string CommandLine::Option::set(std::vector<int32_t>& target, std::string_view name,
                                     std::string_view value) {
    return setIntList(target, name, value, flags);
}

std::string CommandLine::Option::set(std::vector<uint32_t>& target, std::string_view name,
                                     std::string_view value) {
    return setIntList(target, name, value, flags);
}

std::string CommandLine::Option::set(std::vector<int64_t>& target, std::string_view name,
                                     std::string_view value) {
    return setIntList(target, name, value, flags);
}

std::string CommandLine::Option::set(std::vector<uint64_t>& target, std::string_view name,
                                     std::string_view value) {
    return setIntList(target, name, value, flags);
}

std::string CommandLine::Option::set(std::vector<double>& target, std::string_view name,
                                     std::string_view value) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        std::string error;
        auto result = parseDouble(name, entry, error);
        if (!result)
            return error;

        target.push_back(*result);
    }
    return {};
}

std::string CommandLine::Option::set(std::vector<std::string>& target, std::string_view,
                                     std::string_view value) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem))
        target.emplace_back(entry);
    return {};
}

std::string CommandLine::Option::set(OptionCallback& target, std::string_view,
                                     std::string_view value) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        auto result = target(entry);
        if (!result.empty())
            return result;
    }
    return {};
}

std::string CommandLine::addIgnoreCommand(std::string_view value) {
    const size_t firstCommaIndex = value.find_first_of(',');
    const size_t lastCommaIndex = value.find_last_of(',');
    if (firstCommaIndex == std::string_view::npos || firstCommaIndex != lastCommaIndex)
        return fmt::format("missing or extra comma in argument '{}'", value);

    const std::string_view numArgs = value.substr(firstCommaIndex + 1);
    value = value.substr(0, firstCommaIndex);

    std::string error;
    auto result = parseInt<int>("", numArgs, error);
    if (result) {
        cmdIgnore[std::string(value)] = *result;
        return {};
    }
    return error;
}

std::string CommandLine::addRenameCommand(std::string_view value) {
    const size_t firstCommaIndex = value.find_first_of(',');
    const size_t lastCommaIndex = value.find_last_of(',');
    if (firstCommaIndex == std::string_view::npos || firstCommaIndex != lastCommaIndex)
        return fmt::format("missing or extra comma in argument '{}'", value);

    const std::string_view slangName = value.substr(firstCommaIndex + 1);
    value = value.substr(0, firstCommaIndex);
    cmdRename[std::string(value)] = slangName;
    return {};
}

} // namespace slang
