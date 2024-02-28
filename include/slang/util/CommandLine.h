//------------------------------------------------------------------------------
//! @file CommandLine.h
//! @brief Command line argument parsing support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <map>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include "slang/util/Enum.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// Specifies flags that can apply to command line options.
enum class CommandLineFlags {
    /// No special flags.
    None = 0,

    /// The option is for a file path, which should be translated
    /// relative to the current working directory.
    FilePath = 1,

    /// For list options, allow specifying multiple values in
    /// a single entry via a comma-separated list.
    CommaList = 2
};
SLANG_BITMASK(CommandLineFlags, CommaList)

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
class SLANG_EXPORT CommandLine {
public:
    /// Register a flag with @a name that will be parsed as a boolean value,
    /// setting to `true` if no value is provided, and otherwise accepting
    /// the strings "true", "True", "false", and "False" for longform values.
    /// If the flag is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<bool>& value, std::string_view desc,
             bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as an int32.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<int32_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a uint32.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<uint32_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as an int64.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<int64_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a uint64.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<uint64_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a double.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<double>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a string.
    /// If the option is not provided on a command line, the value will remain unset.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::optional<std::string>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of int32s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<int32_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of uint32s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<uint32_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of int64s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<int64_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of uint64s.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<uint64_t>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of doubles.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<double>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Register an option with @a name that will be parsed as a list of strings.
    /// If the option is not provided on a command line, the value will remain an empty vector.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param value a value that will be set if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, std::vector<std::string>& value, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    using OptionCallback = std::function<std::string(std::string_view)>;

    /// Register an option with @a name that will be parsed as a string and
    /// forwarded to the given @a cb callback function for handling.
    /// If the option is not provided on a command line, the callback
    /// will never be invoked.
    ///
    /// @param name a comma separated list of long form and short form names
    ///             (including the dashes) that are accepted for this option
    /// @param cb a callback that will be invoked if the option is provided
    /// @param desc a human-friendly description for printing help text
    /// @param valueName an example name for the value when printing help text
    /// @param flags additional flags that control how the option behaves
    void add(std::string_view name, OptionCallback cb, std::string_view desc,
             std::string_view valueName = {}, bitmask<CommandLineFlags> flags = {});

    /// Set a variable that will receive any positional arguments provided
    /// on the command line. They will be returned as a list of strings.
    ///
    /// @param values a vector of strings that will contain all provided
    ///               positional arguments
    /// @param valueName for including in the help text
    /// @param flags additional flags that control how the option behaves
    /// @note only one variable or callback be set to receive positional arguments
    void setPositional(std::vector<std::string>& values, std::string_view valueName,
                       bitmask<CommandLineFlags> flags = {});

    /// Set a callback that will receive any positional arguments provided
    /// on the command line.
    ///
    /// @param cb a callback that will be invoked for each position argument
    /// @param valueName for including in the help text
    /// @param flags additional flags that control how the option behaves
    /// @note only one variable or callback be set to receive positional arguments
    void setPositional(const OptionCallback& cb, std::string_view valueName,
                       bitmask<CommandLineFlags> flags = {});

    /// Adds a command that will be ignored if encountered during argument parsing.
    ///
    /// @param value a string containing a single comma-separated "name,value" pair,
    ///              where the name is the argument to ignore (including any leading
    ///              '+' and '-' characters) and the value is an integer indicating the
    ///              (possibly zero) number of arguments to ignore following it in the
    ///              argument list.
    /// @returns a string containing an error message if the @a value is malformed.
    std::string addIgnoreCommand(std::string_view value);

    /// Adds a command that will be renamed to one of the existing commands already registered.
    ///
    /// @param value a string containing a single comma-separated "from,to" pair, where the
    ///              "from" is the command that should be renamed whenever encountered in the
    ///              argument list (including any leading '+' and '-' characters), and "to" is
    ///              the new name it should have.
    /// @returns a string containing an error message if the @a value is malformed.
    std::string addRenameCommand(std::string_view value);

    /// Parse the provided command line (C-style).
    /// @return true on success, false if an errors occurs.
    bool parse(int argc, const char* const argv[]);

    /// Contains various options to control parsing of command flags.
    struct ParseOptions {
        /// If set to true, comments will be parsed and ignored.
        /// Comments start with '#' or '//' for line comments and
        /// '/*' and '*/' for block comments.
        bool supportComments = false;

        /// If set to true, don't consider the first argument
        /// to be the name of the program.
        bool ignoreProgramName = false;

        /// If set to true, expand any environment variables found,
        /// with the supported forms $VAR, $(VAR), and ${VAR}.
        bool expandEnvVars = false;

        /// If set to true, don't issue an error if a duplicate
        /// argument setter is found.
        bool ignoreDuplicates = false;

        ParseOptions() {}
    };

    /// Parse the provided command line (space delimited, with handling of
    /// quoted arguments).
    /// @return true on success, false if an errors occurs.
    bool parse(std::string_view argList, ParseOptions options = {});

    /// Parse the provided command line (as a pre-separated list of strings).
    /// @return true on success, false if an errors occurs.
    bool parse(std::span<const std::string_view> args, ParseOptions options = {});

    /// Gets the name of the program, parsed out of the first item on the command line.
    std::string_view getProgramName() const { return programName; }

    /// Manually set the program name for later use in help text.
    void setProgramName(std::string_view name) { programName = name; }

    /// Gets the set of errors that were encountered when parsing command line options.
    std::span<const std::string> getErrors() const { return errors; }

    /// Gets a string representing program help text, based on registered flags.
    /// @a overview text is a human friendly description of what the program does.
    std::string getHelpText(std::string_view overview) const;

private:
    using OptionStorage =
        std::variant<std::optional<bool>*, std::optional<int32_t>*, std::optional<uint32_t>*,
                     std::optional<int64_t>*, std::optional<uint64_t>*, std::optional<double>*,
                     std::optional<std::string>*, std::vector<int32_t>*, std::vector<uint32_t>*,
                     std::vector<int64_t>*, std::vector<uint64_t>*, std::vector<double>*,
                     std::vector<std::string>*, OptionCallback>;

    class Option {
    public:
        OptionStorage storage;
        std::string desc;
        std::string valueName;
        std::string allArgNames;
        bitmask<CommandLineFlags> flags;

        bool expectsValue() const;

        std::string set(std::string_view name, std::string_view value, bool ignoreDup);

    private:
        std::string set(std::optional<bool>& target, std::string_view name, std::string_view value);
        std::string set(std::optional<int32_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::optional<uint32_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::optional<int64_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::optional<uint64_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::optional<double>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::optional<std::string>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::vector<int32_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::vector<uint32_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::vector<int64_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::vector<uint64_t>& target, std::string_view name,
                        std::string_view value);
        std::string set(std::vector<double>& target, std::string_view name, std::string_view value);
        std::string set(std::vector<std::string>& target, std::string_view name,
                        std::string_view value);
        std::string set(OptionCallback& target, std::string_view name, std::string_view value);

        template<typename T>
        static constexpr bool allowValue(const std::optional<T>& target) {
            return !target.has_value();
        }

        template<typename T>
        static constexpr bool allowValue(const std::vector<T>&) {
            return true;
        }
    };

    void addInternal(std::string_view name, OptionStorage storage, std::string_view desc,
                     std::string_view valueName, bitmask<CommandLineFlags> flags);

    void parseStr(std::string_view argList, ParseOptions options, bool& hasArg,
                  std::string& current, SmallVectorBase<std::string>& storage);

    void handleArg(std::string_view arg, Option*& expectingVal, std::string& expectingValName,
                   bool& hadUnknowns, ParseOptions options);
    void handlePlusArg(std::string_view arg, ParseOptions options, bool& hadUnknowns);

    Option* findOption(std::string_view arg, std::string_view& value) const;
    Option* tryGroupOrPrefix(std::string_view& arg, std::string_view& value, ParseOptions options);
    std::string findNearestMatch(std::string_view arg) const;

    std::shared_ptr<Option> positional;
    std::map<std::string, std::shared_ptr<Option>> optionMap;
    std::vector<std::shared_ptr<Option>> orderedOptions;

    // A map of commands to be ignored.
    // key is the command name (including any leading +/- symbols)
    // value is an the number of arguments to be skipped (int)
    // If argument begins with a '+' then matching will ignore anything after a 2nd '+'
    // so that +vendorXYZ+vendorARG can be ignored by matching against +vendorXYZ
    std::map<std::string, int> cmdIgnore;

    /// A map of commands to be renamed, pointing to new name
    /// key is the vendor command name (including any leading +/- symbols)
    /// value is the command name to be used instead
    std::map<std::string, std::string> cmdRename;

    std::string programName;
    std::vector<std::string> errors;
};

} // namespace slang
