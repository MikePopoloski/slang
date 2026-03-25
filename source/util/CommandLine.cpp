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

    auto option = std::make_shared<Option>(*this);
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

    positional = std::make_shared<Option>(*this);
    positional->valueName = valueName;
    positional->storage = &values;
    positional->flags = flags;
}

void CommandLine::setPositional(const OptionCallback& cb, std::string_view valueName,
                                bitmask<CommandLineFlags> flags) {
    if (positional)
        SLANG_THROW(std::runtime_error("Can only set one positional argument"));

    positional = std::make_shared<Option>(*this);
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

bool CommandLine::parse(std::string_view argList, const ParseOptions& options) {
    TokenBuilder builder(options.sourceBuffer);
    tokenize(argList, options, builder);
    builder.finish();

    return parseImpl(builder.getTokens(), options);
}

void CommandLine::TokenBuilder::setPending(const char* ptr) {
    if (!hasArg) {
        SourceLocation loc;
        if (overrideLoc)
            loc = *overrideLoc;
        else if (buffer)
            loc = {buffer.id, uint64_t(ptr - buffer.data.data())};
        tokens.push_back({{}, loc});
        hasArg = true;
    }
}

void CommandLine::TokenBuilder::append(const char* ptr) {
    setPending(ptr);
    current += *ptr;
}

void CommandLine::TokenBuilder::append(const char* ptr, const std::string& value) {
    setPending(ptr);
    current.append(value);
}

void CommandLine::TokenBuilder::finish() {
    if (hasArg) {
        storage.emplace_back(std::move(current));
        tokens.back().str = storage.back();
        current.clear();
        hasArg = false;
    }
}

void CommandLine::TokenBuilder::setOverrideLoc(const char* ptr) {
    if (!overrideLoc && buffer)
        overrideLoc = {buffer.id, uint64_t(ptr - buffer.data.data())};
}

void CommandLine::TokenBuilder::clearOverrideLoc() {
    overrideLoc.reset();
}

void CommandLine::tokenize(std::string_view argList, const ParseOptions& options,
                           TokenBuilder& builder) {
    auto ptr = argList.data();
    auto end = ptr + argList.size();
    while (ptr != end) {
        // Whitespace breaks up arguments.
        char c = *ptr++;
        if (isWhitespace(c) || c == '\0') {
            builder.finish();
            continue;
        }

        // Check for and consume comments.
        if (options.supportComments && (c == '#' || c == '/')) {
            // Slash character only applies if we aren't building an argument already.
            // The hash always applies, even if adjacent to an argument.
            if (c == '#') {
                builder.finish();
                while (ptr != end && !isNewline(*ptr))
                    ptr++;
                continue;
            }

            if (!builder.isPending() && ptr != end) {
                if (*ptr == '/') {
                    builder.finish();
                    ptr++;
                    while (ptr != end && !isNewline(*ptr))
                        ptr++;
                    continue;
                }
                else if (*ptr == '*') {
                    builder.finish();
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

            // All tokens expanded from the env variable get
            // the location of the '$'.
            builder.setOverrideLoc(ptr - 1);

            ParseOptions newOptions = options;
            newOptions.expandEnvVars = false;
            newOptions.sourceBuffer = SourceBuffer{};
            tokenize(result, newOptions, builder);

            builder.clearOverrideLoc();
            continue;
        }

        // Escape character preserves the value of the next character.
        if (c == '\\') {
            if (ptr != end && *ptr != '\n' && *ptr != '\r')
                builder.append(ptr++);
            continue;
        }

        // Any non-whitespace character here means we are building an argument.
        // This is necessary because the quote handling below might create an
        // empty string which should still be recognized as an argument.
        builder.setPending(ptr - 1);

        // Single quotes consume all characters until the next single quote.
        if (c == '\'') {
            while (ptr != end) {
                c = *ptr++;
                if (c == '\'')
                    break;
                builder.append(ptr - 1);
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
                    builder.append(ptr - 1, OS::parseEnvVar(ptr, end));
                else
                    builder.append(ptr - 1);
            }
            continue;
        }

        // Otherwise we just have a normal character.
        builder.append(ptr - 1);
    }
}

bool CommandLine::parse(std::span<const std::string_view> args, const ParseOptions& options) {
    SmallVector<ArgToken, 8> tokens(args.size(), UninitializedTag{});
    for (auto arg : args)
        tokens.push_back({arg, {}});
    return parseImpl(tokens, options);
}

bool CommandLine::parseImpl(std::span<const ArgToken> args, const ParseOptions& options) {
    if (optionMap.empty())
        SLANG_THROW(std::runtime_error("No options defined"));

    if (!options.ignoreProgramName) {
        if (args.empty())
            SLANG_THROW(std::runtime_error("Expected at least one argument"));

        programName = getU8Str(fs::path(args[0].str).filename());
        args = args.subspan(1);
    }

    Option* expectingVal = nullptr;
    ArgToken expectingValToken;
    ArgToken firstPositional;
    bool doubleDash = false;
    bool hadUnknowns = false;

    int skip = 0;
    for (auto& token : args) {
        // Skip N arguments if needed (set by the cmdIgnore feature).
        if (skip) {
            skip--;
            continue;
        }

        auto arg = token.str;
        auto loc = token.loc;

        // If we were previously expecting a value, set that now.
        if (expectingVal) {
            expectingVal->set(expectingValToken.str, arg, options.ignoreDuplicates, loc);
            expectingVal = nullptr;
            continue;
        }

        // This is a positional argument if:
        // - Doesn't start with '-' and '+'
        // - Is exactly '-'
        // - Or we've seen a double dash already
        if (arg.length() <= 1 || doubleDash || (arg[0] != '-' && arg[0] != '+')) {
            if (firstPositional.str.empty())
                firstPositional = token;

            if (positional)
                positional->set(""sv, arg, options.ignoreDuplicates, loc);

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
            bool isPlusArg = false;
            if (arg[0] == '+') {
                // If we ignore a vendor command of the form +xx ,
                // we match on any +xx+yyy command as +yy is the command's argument.
                isPlusArg = true;
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
                auto renamed = it->second + std::string(remainder);
                if (!it->second.empty() && !remainder.empty()) {
                    if (isPlusArg && it->second[0] != '+') {
                        // Renaming a plus arg to a non-plus arg.
                        remainder = remainder.substr(1);
                        while (!remainder.empty()) {
                            size_t plusIndex = remainder.find_first_of('+');
                            renamed = it->second + '=' +
                                      std::string(remainder.substr(0, plusIndex));

                            handleArg(renamed, expectingVal, expectingValToken, hadUnknowns,
                                      options, loc);

                            if (plusIndex == std::string_view::npos)
                                break;

                            remainder = remainder.substr(plusIndex + 1);
                        }
                        continue;
                    }

                    if (!isPlusArg && it->second[0] == '+') {
                        // Renaming a non-plus arg to a plus arg.
                        renamed = it->second + '+' + std::string(remainder.substr(1));
                    }
                }

                handleArg(renamed, expectingVal, expectingValToken, hadUnknowns, options, loc);
                continue;
            }
        }

        // Otherwise just handle the argument.
        handleArg(arg, expectingVal, expectingValToken, hadUnknowns, options, loc);
    }

    if (expectingVal) {
        addError(fmt::format("no value provided for argument '{}'", expectingValToken.str),
                 expectingValToken.loc);
    }

    if (!positional && !firstPositional.str.empty() && !hadUnknowns) {
        addError(fmt::format("positional arguments are not allowed (see e.g. '{}')",
                             firstPositional.str),
                 firstPositional.loc);
    }

    return errors.empty();
}

void CommandLine::handleArg(std::string_view arg, Option*& expectingVal,
                            ArgToken& expectingValToken, bool& hadUnknowns,
                            const ParseOptions& options, SourceLocation loc) {
    // Handle plus args, which are treated differently from all others.
    if (arg[0] == '+') {
        handlePlusArg(arg, options, hadUnknowns, loc);
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
        option = tryGroupOrPrefix(name, value, options, loc);
        if (option)
            arg = name;
    }

    // If we still didn't find it, that's an error.
    if (!option) {
        // Try to find something close to give a better error message.
        auto error = fmt::format("unknown command line argument '{}'", arg);
        auto nearest = findNearestMatch(arg);
        if (!nearest.empty())
            error += fmt::format(", did you mean '{}'?", nearest);

        hadUnknowns = true;
        addError(std::move(error), loc);
        return;
    }

    // Otherwise, we found what we wanted. If we have a value already, go ahead
    // and set it. Otherwise if we're expecting a value, assume that it will come
    // in the next argument.
    if (value.empty() && option->expectsValue()) {
        expectingVal = option;
        expectingValToken = {arg, loc};
    }
    else {
        option->set(arg, value, options.ignoreDuplicates, loc);
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

void CommandLine::handlePlusArg(std::string_view arg, const ParseOptions& options,
                                bool& hadUnknowns, SourceLocation loc) {
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
        addError(fmt::format("unknown command line argument '{}'", arg), loc);
        return;
    }

    auto option = it->second.get();
    if (value.empty()) {
        if (option->expectsValue())
            addError(fmt::format("no value provided for argument '{}'", arg), loc);
        else
            option->set(arg, value, options.ignoreDuplicates, loc);
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

        option->set(arg, curr, options.ignoreDuplicates, loc);

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
                                                   const ParseOptions& options,
                                                   SourceLocation loc) {
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
        option->set(name, ""sv, options.ignoreDuplicates, loc);
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

        int dist = editDistance(key, arg, bestDistance);
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

void CommandLine::addError(std::string msg, SourceLocation loc) {
    errors.push_back({std::move(msg), loc});
}

bool CommandLine::Option::expectsValue() const {
    return storage.index() != 0;
}

void CommandLine::Option::set(std::string_view name, std::string_view value, bool ignoreDup,
                              SourceLocation loc) {
    std::string pathMem;
    if (flags.has(CommandLineFlags::FilePath) && !value.empty() && value != "-" &&
        !value.starts_with("..."sv)) {

        std::error_code ec;
        fs::path path = fs::weakly_canonical(value, ec);
        if (!ec) {
            pathMem = getU8Str(path);
            value = pathMem;
        }
    }

    std::visit(
        [&](auto&& arg) {
            if constexpr (std::is_same_v<OptionCallback, std::decay_t<decltype(arg)>>) {
                set(arg, name, value, loc);
            }
            else {
                if (!allowValue(*arg)) {
                    if (!ignoreDup) {
                        parent.addError(
                            fmt::format("more than one value provided for argument '{}'", name),
                            loc);
                    }
                }
                else {
                    set(*arg, name, value, loc);
                }
            }
        },
        storage);
}

std::optional<bool> CommandLine::parseBool(std::string_view name, std::string_view value,
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

std::optional<bool> CommandLine::Option::parseBool(std::string_view name, std::string_view value,
                                                   SourceLocation loc) {
    std::string err;
    if (auto result = CommandLine::parseBool(name, value, err))
        return result;

    parent.addError(std::move(err), loc);
    return {};
}

template<typename T>
static std::optional<T> parseIntImpl(std::string_view name, std::string_view value,
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

template<typename T>
std::optional<T> CommandLine::Option::parseInt(std::string_view name, std::string_view value,
                                               SourceLocation loc) {
    std::string error;
    auto result = parseIntImpl<T>(name, value, error);
    if (!result)
        parent.addError(std::move(error), loc);
    return result;
}

std::optional<double> CommandLine::Option::parseDouble(std::string_view name,
                                                       std::string_view value, SourceLocation loc) {
    if (value.empty()) {
        parent.addError(fmt::format("expected value for argument '{}'", name), loc);
        return {};
    }

    size_t pos;
    std::optional<double> val = strToDouble(value, &pos);
    if (!val || pos != value.size()) {
        parent.addError(fmt::format("invalid value '{}' for float argument '{}'", value, name),
                        loc);
        return {};
    }

    return val;
}

void CommandLine::Option::set(std::optional<bool>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseBool(name, value, loc);
}

void CommandLine::Option::set(std::optional<int32_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseInt<int32_t>(name, value, loc);
}

void CommandLine::Option::set(std::optional<uint32_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseInt<uint32_t>(name, value, loc);
}

void CommandLine::Option::set(std::optional<int64_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseInt<int64_t>(name, value, loc);
}

void CommandLine::Option::set(std::optional<uint64_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseInt<uint64_t>(name, value, loc);
}

void CommandLine::Option::set(std::optional<double>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    target = parseDouble(name, value, loc);
}

void CommandLine::Option::set(std::optional<std::string>& target, std::string_view,
                              std::string_view value, SourceLocation) {
    target = value;
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
void CommandLine::Option::setIntList(std::vector<T>& target, std::string_view name,
                                     std::string_view value, SourceLocation loc) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        auto result = parseInt<T>(name, entry, loc);
        if (!result)
            return;
        target.push_back(*result);
    }
}

void CommandLine::Option::set(std::vector<int32_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    setIntList(target, name, value, loc);
}

void CommandLine::Option::set(std::vector<uint32_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    setIntList(target, name, value, loc);
}

void CommandLine::Option::set(std::vector<int64_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    setIntList(target, name, value, loc);
}

void CommandLine::Option::set(std::vector<uint64_t>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    setIntList(target, name, value, loc);
}

void CommandLine::Option::set(std::vector<double>& target, std::string_view name,
                              std::string_view value, SourceLocation loc) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        auto result = parseDouble(name, entry, loc);
        if (!result)
            return;
        target.push_back(*result);
    }
}

void CommandLine::Option::set(std::vector<std::string>& target, std::string_view,
                              std::string_view value, SourceLocation) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem))
        target.emplace_back(entry);
}

void CommandLine::Option::set(OptionCallback& target, std::string_view, std::string_view value,
                              SourceLocation loc) {
    SmallVector<std::string_view> splitMem;
    for (auto entry : parseList(value, flags.has(CommandLineFlags::CommaList), splitMem)) {
        auto result = target(entry);
        if (!result.empty()) {
            parent.addError(std::move(result), loc);
            return;
        }
    }
}

std::string CommandLine::addIgnoreCommand(std::string_view value) {
    const size_t firstCommaIndex = value.find_first_of(',');
    const size_t lastCommaIndex = value.find_last_of(',');
    if (firstCommaIndex == std::string_view::npos || firstCommaIndex != lastCommaIndex)
        return fmt::format("missing or extra comma in argument '{}'", value);

    const std::string_view numArgs = value.substr(firstCommaIndex + 1);
    value = value.substr(0, firstCommaIndex);

    std::string error;
    auto result = parseIntImpl<int>("", numArgs, error);
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

std::string CommandLine::toKebabCase(std::string_view str) {
    std::string result;
    for (size_t i = 0; i < str.size(); ++i) {
        char c = str[i];
        if (i > 0 && std::isupper(c))
            result += '-';
        result += charToLower(c);
    }
    return result;
}

} // namespace slang
