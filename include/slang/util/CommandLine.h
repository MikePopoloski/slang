//------------------------------------------------------------------------------
//! @file CommandLine.h
//! @brief Command line argument parsing support
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <map>
#include <string>
#include <variant>
#include <vector>

#include "slang/util/Util.h"

namespace slang {

/// Command line argument parser.
///
/// Arguments are parsed in the general style of GNU longopts.
/// Each option name can be any combination of short and long form,
/// where short forms start with a single dash and are a single letter,
/// and long forms start with a double dash and can be multiple letters.
///
/// All options (besides boolean flags) require a value to be passed as well.
/// Values can be passed as whitespace separated strings. For example:
/// `-f 1 --long 2`
///
/// For long form names, values can be passed with an '=' sign followed by
/// the value instead:
/// `--long=2`
///
/// For short form names, values can be passed directly adjacent in the string,
/// no whitespace required:
/// `-f1`
///
/// Groups of short form names can be combined together. The final short
/// form name in such a group can have an adjacent value:
/// `-abcf1`
///
/// Options can alternatively begin with a '+', in which case they are
/// always long form, and expect their value(s) to come separated by
/// additional '+' signs. For example:
/// `+opt+val1+val2`
///
/// A standalone double dash, "--", indicates that all further elements of
/// the command line are to be considered positional and not parsed as options.
/// A single dash, "-", is always considered to be a positional argument.
///
/// If a provided option on the command line does not match any registered name,
/// an error is reported. If the name is "close" to one of the registered names,
/// the error will provide a helpful "did you mean" hint.
///
class CommandLine {
public:
    /// Register a flag with @a name that will be parsed as a boolean value,
    /// setting to `true` if no value is provided, and otherwise accepting
    /// the strings "true", "True", "false", and "False" for longform values.
    /// If the flag is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    void add(string_view name, optional<bool>& value, string_view desc);

    /// Register an option with @a name that will be parsed as an int32.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<int32_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a uint32.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<uint32_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as an int64.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<int64_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a uint64.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<uint64_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a double.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<double>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a string.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, optional<std::string>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of int32s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<int32_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of uint32s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<uint32_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of int64s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<int64_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of uint64s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<uint64_t>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of doubles.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<double>& value, string_view desc,
             string_view valueName = {});

    /// Register an option with @a name that will be parsed as a list of strings.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @name is a comma separated list of long form and short form names
    /// (including the dashes) that are accepted for this option.
    /// @a desc is a human-friendly description for printing help text.
    /// @a valueName is an example name for the value when printing help text.
    void add(string_view name, std::vector<std::string>& value, string_view desc,
             string_view valueName = {});

    /// Set a variable that will receive any positional arguments provided
    /// on the command line. They will be returned as a list of strings.
    /// @valueName is for including in the help text.
    void setPositional(std::vector<std::string>& values, string_view valueName);

    /// Parse the provided command line (C-style).
    /// @return true on success, false if an errors occurs.
    bool parse(int argc, const char* const argv[]);

    /// Parse the provided command line (space delimited, with handling of
    /// quoted arguments).
    /// @return true on success, false if an errors occurs.
    bool parse(string_view argList);

    /// Parse the provided command line (as a pre-separated list of strings).
    /// @return true on success, false if an errors occurs.
    bool parse(span<const string_view> args);

#if defined(_MSC_VER)
    /// Parse the provided command line (MSVC wchar-style).
    /// @return true on success, false if an errors occurs.
    bool parse(int argc, const wchar_t* const argv[]);
#endif

    /// Gets the name of the program, parsed out of the first item on the command line.
    string_view getProgramName() const { return programName; }

    /// Manually set the program name for later use in help text.
    void setProgramName(string_view name) { programName = name; }

    /// Gets the set of errors that were encountered when parsing command line options.
    span<const std::string> getErrors() const { return errors; }

    /// Gets a string representing program help text, based on registered flags.
    /// @a overview text is a human friendly description of what the program does.
    std::string getHelpText(string_view overview) const;

private:
    using OptionStorage =
        std::variant<optional<bool>*, optional<int32_t>*, optional<uint32_t>*, optional<int64_t>*,
                     optional<uint64_t>*, optional<double>*, optional<std::string>*,
                     std::vector<int32_t>*, std::vector<uint32_t>*, std::vector<int64_t>*,
                     std::vector<uint64_t>*, std::vector<double>*, std::vector<std::string>*>;

    class Option {
    public:
        OptionStorage storage;
        std::string desc;
        std::string valueName;
        std::string allArgNames;

        bool expectsValue() const;

        std::string set(string_view name, string_view value);

    private:
        std::string set(optional<bool>& target, string_view name, string_view value);
        std::string set(optional<int32_t>& target, string_view name, string_view value);
        std::string set(optional<uint32_t>& target, string_view name, string_view value);
        std::string set(optional<int64_t>& target, string_view name, string_view value);
        std::string set(optional<uint64_t>& target, string_view name, string_view value);
        std::string set(optional<double>& target, string_view name, string_view value);
        std::string set(optional<std::string>& target, string_view name, string_view value);
        std::string set(std::vector<int32_t>& target, string_view name, string_view value);
        std::string set(std::vector<uint32_t>& target, string_view name, string_view value);
        std::string set(std::vector<int64_t>& target, string_view name, string_view value);
        std::string set(std::vector<uint64_t>& target, string_view name, string_view value);
        std::string set(std::vector<double>& target, string_view name, string_view value);
        std::string set(std::vector<std::string>& target, string_view name, string_view value);

        template<typename T>
        static constexpr bool allowValue(const optional<T>& target) {
            return !target.has_value();
        }

        template<typename T>
        static constexpr bool allowValue(const std::vector<T>&) {
            return true;
        }
    };

    void addInternal(string_view name, OptionStorage storage, string_view desc,
                     string_view valueName);

    void handlePlusArg(string_view arg, bool& hadUnknowns);

    Option* findOption(string_view arg, string_view& value) const;
    Option* tryGroupOrPrefix(string_view& arg, string_view& value);
    std::string findNearestMatch(string_view arg) const;

    std::shared_ptr<Option> positional;
    std::map<std::string, std::shared_ptr<Option>> optionMap;
    std::vector<std::shared_ptr<Option>> orderedOptions;

    std::string programName;
    std::vector<std::string> errors;
};

} // namespace slang
