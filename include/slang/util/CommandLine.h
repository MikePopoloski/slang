//------------------------------------------------------------------------------
// CommandLine.h
// Command line argument parsing support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

class CommandLine {
public:
    void add(string_view name, optional<bool>& value, string_view desc);
    void add(string_view name, optional<int32_t>& value, string_view desc, string_view valueName);
    void add(string_view name, optional<uint32_t>& value, string_view desc, string_view valueName);
    void add(string_view name, optional<int64_t>& value, string_view desc, string_view valueName);
    void add(string_view name, optional<uint64_t>& value, string_view desc, string_view valueName);
    void add(string_view name, optional<double>& value, string_view desc, string_view valueName);
    void add(string_view name, optional<std::string>& value, string_view desc,
             string_view valueName);

    void add(string_view name, std::vector<bool>& value, string_view desc);
    void add(string_view name, std::vector<int32_t>& value, string_view desc,
             string_view valueName);
    void add(string_view name, std::vector<uint32_t>& value, string_view desc,
             string_view valueName);
    void add(string_view name, std::vector<int64_t>& value, string_view desc,
             string_view valueName);
    void add(string_view name, std::vector<uint64_t>& value, string_view desc,
             string_view valueName);
    void add(string_view name, std::vector<double>& value, string_view desc, string_view valueName);
    void add(string_view name, std::vector<std::string>& value, string_view desc,
             string_view valueName);

    void setPositional(std::vector<std::string>& values, string_view valueName);

    bool parse(int argc, const char* const argv[]);
    bool parse(int argc, const wchar_t* const argv[]);
    bool parse(string_view argList);
    bool parse(span<const string_view> args);

    string_view getProgramName() const { return programName; }
    void setProgramName(string_view name) { programName = name; }

    span<const std::string> getErrors() const { return errors; }

private:
    using OptionStorage =
        std::variant<optional<bool>*, optional<int32_t>*, optional<uint32_t>*, optional<int64_t>*,
                     optional<uint64_t>*, optional<double>*, optional<std::string>*,
                     std::vector<bool>*, std::vector<int32_t>*, std::vector<uint32_t>*,
                     std::vector<int64_t>*, std::vector<uint64_t>*, std::vector<double>*,
                     std::vector<std::string>*>;

    struct Option {
        OptionStorage storage;
        std::string desc;
        std::string valueName;

        void set(string_view value);
    };

    void addInternal(string_view name, OptionStorage storage, string_view desc,
                     string_view valueName);

    Option* findOption(string_view arg, string_view& value) const;
    Option* tryGroupOrPrefix(string_view& arg, string_view& value);
    string_view findNearestMatch(string_view arg) const;

    std::shared_ptr<Option> positional;
    std::unordered_map<std::string, std::shared_ptr<Option>> optionMap;

    std::string programName;
    std::vector<std::string> errors;
};

} // namespace slang