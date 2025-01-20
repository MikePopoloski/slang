# slang-tidy

A SystemVerilog linter

## Configuration File

Slang Tidy can be configured using a `.slang-tidy`. This file can be provided using the `--config-file` argument or the
`slang-tidy` tool will search for it from the path where it has been called until the root directory.

### Configuration file grammar

The grammar of the config file is the following

```
config                ::= section+
section               ::= checks_config_section | checks_section
checks_section        ::= "Checks:" [EOL] rule+
rule                  ::= ["-"] ((check_or_all ",")* | check_or_all) END
check_or_all          ::= "*" | check_group "-" check_name_or_all
check_group           ::= identifier
check_name_or_all     ::= "*" | identifier
checks_config_section ::= "CheckConfigs:" [EOL] config+
config                ::= ((config_tuple ",")* | config_tuple) END
config_tuple          ::= config_name ":" config_value
config_name           ::= identifier
config_value          ::= expression | "[" ((expression ",")* expression)? "]"
identifier            ::= { A-Z | a-z }+
expression            ::= { A-Z | a-z | 0-9 | "_" }+
EOL                   ::= '\n' | '\r' | '\r\n'
END                   ::= EOL* | EOF
```

### Configuration file

The syntax of the `.slang-tidy` file is similar to the syntax of the `.clang-tidy`. There are two main
sections: `Checks` and `CheckConfigs`, that can appear as many times as needed in the config file.

The `Checks` section is a comma separated list of globs with an optional `-` prefix, that will enable or disable
the specified check or group of checks.

```
Enable a check: synthesis-only-assigned-on-reset

Disable a check: -synthesis-only-assigned-on-reset

Enable a group: synthesis-*

Disable a group: -synthesis-*

Enable all: *

Disable all: -*
```

The `CheckConfigs` is a dictionary like, `config: value`, comma separated list of options for the different checks.
The available options are:

|            Config             |   Type   |      Default       |
|:-----------------------------:|:--------:|:------------------:|
|          **clkName**          |  string  |       clk_i        |
|    **clkNameRegexString**     |  string  | \"clk\\S*\|clock\\S*\" |
|         **resetName**         |  string  |      rst_ni        |
|     **resetIsActiveHigh**     |   bool   |       true         |
|      **inputPortSuffix**      | [string] |       [_i]         |
|     **outputPortSuffix**      | [string] |       [_o]         |
|      **inoutPortSuffix**      | [string] |       [_io]        |
| **moduleInstantiationPrefix** |  string  |        i_          |

An example of a possible configuration file:

```
Checks:
    -*,
    synthesis-only-assigned-on-reset,
    style-enforce-port-suffix

CheckConfigs:
    clkName: clk,
    clkNameRegexString: "clk_signal\S*|clock_port\S*",
    resetIsActiveHigh: false,
    inputPortSuffix: _k,
    outputPortSuffix: _p
```

## How to add a new check

1. Create a new `cpp` file with the name of the check in CamelCase format inside the check kind folder.
2. Inside the new `cpp` file create a class that inherits from `TidyChecks`. Use the `check` function to implement
   the code that will perform the check in the AST.
3. Use the `REGISTER` macro to register the new check in the factory.
4. Create the new tidy diagnostic in the `TidyDiags.h` file.
5. Add the new check to the corresponding map in the `TidyConfig` constructor.
6. Update the documentation accordingly
7. Add the new `cpp` file to CMakeLists.txt
