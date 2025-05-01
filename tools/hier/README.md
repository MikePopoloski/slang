slang-hier
==========
A tool that can display information about a Verilog hierarchy.

This tool accepts the standard set of slang driver command line options,
which lets you configure your design. Then the tool will display
information like module instance names and resolved parameter values.

Additional options to control output:

`--params`

Include instance parameter values in the output.

`--max-depth <depth>`

The maximum instance depth of the hierarchy to be printed.
Everything deeper than that will be ignored.

`--inst-prefix <prefix>`

A hierarchical path indicating which hierarchy to display.
All parts of the design not under this prefix will be ignored.

`--inst-regex <regex>`

Only instances that match the given regex (anywhere in the design tree)
will be shown. All others will be skipped.

`--custom-format <fmt>`

A libfmt style format string that controls how the output is printed.
Use `{inst}`, `{module}`, `{file}` as argument names in the string.
