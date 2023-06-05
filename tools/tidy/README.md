# Slang Tidy

A SystemVerilog linter

## Configuration File

Slang Tidy can be configured using a `.slang-tidy` file located on the root of the project
or by providing the path of the file using `--config-file`.

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
config_value          ::= identifier
identifier            ::= {A-Za-z}+
EOL                   ::= '\n' | '\r' | '\r\n'
END                   ::= EOL | EOF
```

### Configuration file example

```
Checks:
    -synthesis-only-assigned-on-reset,
    -ports-enforce-port-suffix
CheckConfigs:
    clkName: clk,
    resetIsActiveHigh: false,
    inputPortSuffix: _k,
    inputPortSuffix: _p
```
