# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]
### Language Support
### General Features
### Improvements
### Fixes


## [v4.0] - 2023-08-10
### Language Support
* Finished full support for user-defined primitives by adding error checking for table entries
* Support for whitespace between the two characters of the dist weight operators has been added for compatibility with other tools -- this is an error by default but can be downgraded as needed. See [-Wsplit-distweight-op](https://sv-lang.com/warning-ref.html#split-distweight-op).
* Added support for net aliases
* Added support for checkers
* Added support for extern modules/interfaces/programs/primitives, along with wildcard port lists in declaration headers

### General Features
* slang now requires a C++20 compatible compiler to build (e.g. minimum GCC 10)
* New warnings [-Wport-width-expand](https://sv-lang.com/warning-ref.html#port-width-expand) and [-Wport-width-trunc](https://sv-lang.com/warning-ref.html#port-width-trunc) separate out width warnings that occur in port connections from general expressions elsewhere. This makes it easier to find and target these specific cases of width mismatches.
* New option `--suppress-macro-warnings` that functions similarly to `--suppress-warnings` except that it applies to the original definition location of macros instead of their expansion location. This is useful if, for example, you want to hide warnings from 3rd party macros (like from UVM) that you use in your own code.
* A new experimental tool called `slang-netlist` has been added (thanks to @jameshanlon) -- see the [readme](https://github.com/MikePopoloski/slang/blob/master/tools/netlist/README.md) for more details
* A new experimental tool called `slang-reflect` has been added (thanks to @Sustrak) -- see the [readme](https://github.com/MikePopoloski/slang/tree/master/tools/reflect/README.md) for more details
* The slang build optionally supports obtaining dependencies via [conan.io](https://conan.io/) -- see [the docs](https://sv-lang.com/building.html#dependencies) for details.
* The slang driver now accepts [file patterns](https://sv-lang.com/user-manual.html#file-patterns) to make it easier to select groups of files
* Initial support for [source libraries](https://sv-lang.com/user-manual.html#source-libraries) and library map files has been added. This is only for specifying input files right now but in future releases will be expanded to work with SystemVerilog config declarations.

### Improvements
* When dealing with duplicate module/interface/program definitions (where the error has been downgraded to a warning) slang will now make use of the first definition seen instead of any later ones, to better match the behavior of other tools
* Improved the warnings issued for unused 'inout' ports
* Macros declared in slang headers have been namespaced to avoid polluting user code
* Several hash table implementations used by slang (ska::flat_hash_map, unordered_dense, StringTable) have been removed and consolidated into using boost::unordered. The library includes a minimal boost_unordered.hpp header to avoid needing to depend on all of boost.
* Added a dependency on the mimalloc custom allocator (can be disabled if desired)
* A number of small optimizations (including the switch to boost::unordered and use of mimalloc) combine to improve general slang compilation performance by about 10%
* slang can now build correctly with exceptions and RTTI disabled, to allow integration with other codebases that disable use of these features
* The slang driver will now parse input files in multiple threads by default. This can be disabled with `--threads=1`. This feature is not supported when using `--single-unit`.
* The `--libdir` feature will now search for files based on interface port declarations in addition to module instantiations (thanks to @AndrewNolte)
* Support for visitors has been added to the Python bindings (thanks to @tdp2110)
* Low-level file loading routines in slang have been rewritten to use platform-level APIs. This should slightly improve performance, but more importantly it allows slang to report system-specific error messages when file loading fails.
* Failed file loads invoked via the Python bindings now raise an appropriate Python exception
* The `--suppress-warnings` option has been changed to take a file pattern instead of a directory path prefix. Existing uses of this flag will need to be updated to the new behavior.
* Most command line arguments that accept multiple values now accept those values as a comma-separated list in addition to repeating the argument multiple times
* slang can now read input from stdin by specifying a file named '-'

### Fixes
* Fixed a bug that prevented indexing into an interface array when accessing that array hierarchically
* break and continue statements are now correctly disallowed from controlling a loop outside of a fork-join block
* Duplicate driver checking now applies to signals accessed via modports
* Subroutine ports with initializers will now issue an appropriate error
* Subroutine argument default values are now checked for the correct direction and count as drivers for target symbols
* Fixed messaging generated by elaboration system tasks when arguments are invalid
* Fixed an off-by-one error in symbol lookup location for detecting whether parameters are used before they are declared
* Fixed a few return value policies in the Python bindings that were incorrect
* Fixed a bug where a continuous assign statement that referenced an implicit net more than once would cause an error about duplicate net declarations
* Fixed the use of the $global_clocking system functions in direct event controls
* Fixed an erroneous diagnostic when checking which kinds of expressions are allowed in a binary `and` or `or` property expression
* Fixed parsing of tagged patterns when followed immediately by a `&&&` predicate
* Added tests and fixed resulting issues found in AST serialization and visitation methods
* The Compilation constructor now ensures it safely only adds type diagnostic printing callbacks once, to allow multithreaded use of separate Compilation objects
* Fixed the error message reported for -Wimplicit-port-type-mismatch -- it was reporting the wrong types involved
* Fixed parsing of parameter ports that have multiple declarators -- previously later parameters in the list were not being associated with the prior type declaration


## [v3.0] - 2023-03-18
### Highlights
As of this release slang passes 100% of the tests at https://github.com/chipsalliance/sv-tests (the only tool able to do so).

### Language Support
* Added support for specify module timing paths
* Added support for specify pulsestyle and showcancelled directives
* Added support for `PATHPULSE$` specparams
* Added support for system timing checks
* Added support for program namespacing rules
* Added support for anonymous programs
* Added support for DPI open array typed arguments
* Added support for `$inferred_clock` and `$inferred_disable`
* Finished full support for bind directives
* Finished full support for defparams

### General Features
* New option `--obfuscate-ids` when used with `--preprocess` will replace all identifiers in the output with obfuscated alphanumeric strings (thanks to @Sustrak)
* Added a group of new warnings to report on unused code elements; see [-Wunused](https://sv-lang.com/warning-ref.html#unused)
* A new (currently experimental) tool, `slang-tidy`, has been added as a place to collect more in-depth or project-specific static analysis rules (thanks to @Sustrak).
* New option `--suppress-warnings` allows suppressing warnings from one or more file paths, intended to allow easily hiding warnings from 3rd party code

### Improvements
* The default library name for slang has been changed to "libsvlang" to avoid clashing with an existing "S-lang" package on most Linux systems. The library name is now configureable via CMake.
* Errors about unknown package names are now ignored in lint-only mode
* Drastically improved the performance of overlapping driver checking and driver loop unrolling. For large projects this may reduce compile times by as much as 80-90%.
* Net charge strength and drive strength have been added to the AST
* Added human-friendly names for function arguments in Python bindings (thanks to @Kuree)
* Conditional statements in constant functions now implement unique/priority semantics (thanks to @HungMingWu)
* Procedural force/release of bit selects or part selects is an error according to the LRM; this error can now be downgraded to a warning for compatibility with other tools (thanks to @udif)
* Implicit named port connections with inequivalent types are disallowed by the LRM; this error can now be downgraded to a warning for compatibility with other tools
* When printing type names in diagnostics, if more than one type shares the same simple name, they will now be disambiguated with their full path
* A new `--timescale` option allows setting a default time scale for design elements. If this option is not set, there is no default and an error will be
issued if not all elements have a time scale specified (as required by the LRM).

### Fixes
* Parameters used inside specify blocks will now issue an appropriate warning
* Fixed an issue where the parser erroneously allowed selects of integer literal expressions
* Top-level programs are now automatically instantiated, just like top-level modules
* Implicit covergroups declared inside classes were previously not being checked for correctness
* Fixed parser handling of spacing within `always@( *)` statements being misinterpreted as a closing attribute token (thanks to @godblesszhouzhou)
* Fixed a bug in the lookup location used for non-ansi port symbol attribute expressions
* Fixed `-Werror` to actually work
* Tweaked handling of unbased unsized literals to reduce false-positive width warnings
* Changed scoped access to incomplete forward typedefs to be allowed as long as the final name in the chain is not a type (matches behavior of other tools)
* The parser now correctly disallows attributes on assignment operators
* References to compilation unit items from within packages is now correctly disallowed
* Hierarchical references from packages to items outside that package are now correctly disallowed
* Bit-vector system functions (such as `$countbits`) can now be used with bitstream types (as opposed to just integral types)
* Max size limits for packed and unpacked arrays and structs are now strictly enforced
* Invalid inferred time scales will now issue an appropriate error
* Fixed a bug in arithmetic of large constants at compile time (thanks to @adream307)


## [v2.0] - 2022-10-29
### Highlights
This release focuses on making slang much more usable as a library. There's been a large amount of refactoring
and reorganizing to make usage more straightforward. The CMake build was rewritten, and documentation showing how to
integrate the library has been improved. Python bindings have been added to make it easy to use slang in scripts and tools.

### Language Support
* Added support for modport port expressions
* Added support for modport exports and `extern` interface methods (including the rules for `extern forkjoin` methods)
* Directionality of modport ports is now enforced (e.g. assigning to an input modport port is now an error)
* Added full support for SystemVerilog's pattern matching feature, including usage in constant expressions
* Added parsing support for config declarations
* The parser now enforces syntax rules around specify block edge descriptors
* Port connection slicing across arrays of instances is now also allowed with implicit port connections
* Access to static class data members via an incomplete forward typedef is now allowed
* Compile-time constant out-of-bounds element and range selects have always been an error in slang. The LRM allows for them to either be an error or optionally to result in `'x` and compilation to continue -- to support this option the resulting errors have been changed to suppressible warnings (though still set to errors by default).
* `` `pragma protect`` directives are now validated for correctness and encoded text is now decoded by slang (in all four decoding formats mentioned by the LRM). Actual encrypted text is not decrypted but just skipped instead -- it's very unlikely any IP vendor will ever provide slang with a decryption key so there's little point in implementing it.
* Duplicate module / interface / program / primitive definitions have been made a suppressible error to support legacy workflows (thanks to @udif)

### General Features
* New warning: [-Wempty-body](https://sv-lang.com/warning-ref.html#empty-body) (on by default) warns about likely accidental usage of semicolons after a loop or if condition that causes the body to be empty
* New warning: [-Wreversed-range](https://sv-lang.com/warning-ref.html#reversed-range) (on by default) warns about a reversed open range that will behave as if it's an empty set instead
* Added [Python bindings](https://github.com/MikePopoloski/pyslang) for the library
* Driver code has been factored out of the slang-driver tool into a [Driver class](https://sv-lang.com/classslang_1_1driver_1_1_driver.html) that can be consumed by users of the library that are creating their own frontend tools
* slang now treats all input source files as being UTF-8 encoded. Previously slang required all sources to be ASCII encoded but did not strictly enforce that, and could behave incorrectly when encountering non-ASCII characters. Now all characters are validated and UTF-8 sequences are handled correctly (and are allowed without issue inside string literals and code comments). Invalid UTF-8 sequences are diagnosed and a warning will be issued.
* The default set of warnings was tweaked - some were added and some removed. See the [Warning Reference](https://sv-lang.com/warning-ref.html) for more information about which are on by default.
* The `--libraries-inherit-macros` flag was added to allow macros defined in primary source files to bleed over into automatically loaded library files. The `--single-unit` option must also be used when providing this option.
* New options `--cmd-ignore` and `--cmd-rename` can be used when you have existing command files with option flags designed for another tool to process (thanks to @udif)
* New option `--ignore-directive` can be used to ignore vendor-specific preprocessor directives that would otherwise cause slang to flag an error (thanks to @udif)
* Added `--time-trace` to profile where slang is spending its compilation time

### Improvements
* slang now reports a better error when you forget to put parenthesis after a module or interface instantiation
* Lots of internal code cleanup, static analysis and lint fixes, and cleanup of TODOs in this release
* Large integers printed in diagnostics will now be abbreviated to avoid filling the console with tons of digits
* Added a limit to the size of instance arrays, to avoid hangs and running out of memory when typos produce huge array sizes. Use `--max-instance-array` if you run into the limit in a real design.
* Made several improvements to parser error recovery to cover common coding errors
* Several improvements were made to the SyntaxVisitor and SyntaxRewriter helper classes (thanks to @HungMingWu)
* Many improvements were made to the cmake build and installation flow. slang should be much more easily consumed as a library in downstream projects.
* Wrote more documentation and improved the doc build and its presentation
* A lot of code was reorganized internally into more easily discovered locations. Library code is now organized into namespaces.
* slang should now build correctly as a shared library out of the box
* Made several minor optimizations across the library that should add up to about 10-15% compilation speed improvement for typical workflows
* The minimum compiler version for slang was bumped to GCC 9. This will move to GCC 10 (and allow use of C++20 features) after the next release.

### Fixes
* Fixed ICE when a subroutine declaration refers to itself in its own return type declaration
* Fixed several issues with Unicode path handling on Windows
* Fixed a parser bug where a colon followed immediately by a line comment would be parsed incorrectly (thanks to @HungMingWu)
* Fixed a parsing bug with `restrict property` statements
* Fixed several crashes and internal assertions in corner cases discovered by fuzz testing
* Fixed a number of cases where a proper diagnostic in an error scenario would be followed by one or more spurious diagnostics -- now only the one proper diagnostic is issued
* Fixed a number of cases where a diagnostic with a formatted message might put an empty string into that message, which was confusing and not helpful
* Constraint blocks are now correctly disallowed outside of class declarations
* The `$bits` system function can now correctly reference automatic variables from static initializers
* Fixed struct member declarations that referred to other members in the same struct type as part of their type declaration
* Fixed handling of defparams when there are infinitely recursive modules in the design
* The macro list printed by `--macros-only` is now sorted for consistent ordering between runs
* Fixed a bug where diagnostic pragmas were not correctly handled when found in automatically loaded library source files
* Source files listed in command files are now processed strictly in order relative to files listed in other command files, which gives predictable behavior when treating them as a single unit
* The check for maximum include stack depth was erroneously including all files in its count when using single-unit builds
* Fixed a bug that could cause case statements in constant expression to be misevaluated under certain conditions
* Fixed the inferred type of untyped parameters when initialized from an equivalent but not matching type expression
* Fixed a bug in the parser that could misparse delayed statements after an event control expression


## [v1.0] - 2022-06-25
### Highlights
slang can now detect and enforce all of the various rules surrounding multiple drivers on nets, variables, and ports. This release also comes with support for functional coverage constructs, opt-in support for hierarchical names used within constant expressions, and some additional compatibility functionality to make it easier to use with codebases that primarily build with other, less-conformant tools.

As of this release, no pre-built binaries will be included. They were of limited usefulness and difficult to maintain and so it's not worth providing them -- build from the source release instead.

### Language Support
* Added full support for covergroups, cover points, cover crosses, coverage bins and options.
* Added support for untyped mailboxes.
* Hierarchical references can now be used in constant expressions by passing the `--allow-hierarchical-const` flag. This is not strictly legal in SystemVerilog but other tools allow it and so slang supports it for compatibility.
* Added support for non-ansi interface ports.
* Added support for user-defined nettypes in module and interface port lists.
* Added support for non-ansi "multiports" and sliced ports.
* Added support for explicit ansi and non-ansi ports.
* Added support for generic interface ports.
* Added support for nested module and interface declarations.
* Added the LRM rules for port collapsing of dissimilar net types.
* Added rules around multiple drivers or mixed continuous and procedural drivers for variables and uwires.
* Added rules for port connection directions (input vs output).
* Added rules to disallow reading output clock variables or continuous assignments to the target of a clock variable.
* Added rules to disallow assertion local variables from being driven by more than one output local variable formal argument.
* Added rules about what timing controls are allowed in always_comb / always_latch / always_ff.
* Added rules for user-defined nettype resolution functions.
* Added LRM-specified warnings when net port coercion occurs.
* Added full support for interconnect nets.
* Added support for let declarations and nettypes inside of statement blocks.

### General Features
* A missing include directory passed to the driver tool is now a warning instead of an error.
* A `--compat` flag was added to allow specifying general compatibility requirements with other tools. Currently only `vcs` is supported as a value. This enables a bunch of other flags to try to be compatible with VCS as much as possible.
* `+incdir` and `+define` flags were added to increase compatibility with other tools.
* Support for "command files" was added -- use the `-F` and `-f` flags to specify the path to a command file. Command files allow more conveniently specifying large lists of files and command line options to an invocation of the tool. See [Command Files](https://sv-lang.com/user-manual.html#command-files) for more detail.
* Added a $static_assert elaboration task that takes a condition and fails compilation if that condition is false. See [Nonstandard Built-In Functions](https://sv-lang.com/user-manual.html#system-funcs) for an example.
* Added a `--relax-enum-conversions` flag to do less strict type checking of enum conversions, for compatibility with other tools.
* Integer literal overflow is now a warning instead of an error.
* All warning flags are now documented with examples here: [Warning Reference](https://sv-lang.com/warning-ref.html)
* The `-Wno-top` warning flag was renamed to `-Wmissing-top` to avoid confusion with the -no prefix.
* Added a `--allow-dup-initial-drivers` flag which allows duplicate drivers from initial blocks instead of causing an error, for compatibility with other tools.
* By default, procedural `for` loops will be unrolled if possible before checking for duplicate driver errors. The LRM is actually more strict and does not allow this looser form of driver checking, so a `--strict-driver-checking` flag has been added to disable it. More details at [Driver Loop Unrolling](https://sv-lang.com/user-manual.html#loop-unroll).

### Fixes
* A better error is reported when trying to hierarchically refer to a type name.
* `$unit` based names are no longer erroneously considered hierarchical.
* The coverage system functions now allow a standalone `$root` as an argument.
* Finished a bunch of TODOs and corner case handling in port declarations.
* Made several tweaks to the parser's error recovery to get better diagnostics for commonly made mistakes.
* Fixed issues with non-ansi port declarations that used named types.
* Port initializers are now correctly required to be constants.
* The $dumpvars function is now allowed to dump nets as well.
* Fixed ICE when exporting an imported enum member from a package.
* Fixed the printing of hierarchical path names in diagnostics.
* Fixed macro stringification of substituted string literals.
* Parameters with unpacked dimensions are now allowed to have a partially inferred type (with a `logic` base element type).
* Report an error for variables connected to `inout` ports.
* Report an error for unconnected `ref` ports.
* Top-level modules cannot have `ref` ports.
* Fixed JSON serialization of method prototype arguments.
* A better error is reported when trying to assign to a constant.
* Correctly disallow `inout` uwire ports.
* Fixed how subroutine argument types are inferred if not explicitly provided.
* Fixed a bug that allowed some errors in class randomize lookups to go unreported.
* Fixed a double reporting of errors when enums have an invalid base type.
* Fixed selection of enum values that are members of a struct declaration.
* Fixed type compatibility checking for types that share the same source syntax but live in different logical places in the hierarchy.
* Report an error if there are cycles in a class inheritance chain.
* Fixed the threshold for unrecoverable lexer errors to not include warnings in the count.
* Fixed some corner cases where lvalues of system methods were not properly validated.
* Correctly error if there are duplicate out-of-block class method definitions.
* Correctly require for loop variable declarations to have initializers.
* Fixed a few parsing corner cases for user-defined primitives.
* Correctly disallow assertion local variables from being referenced in event expressions.
* Fixed an incorrect implicit conversion of string literals inside of concatenation expressions.


## [v0.9] - 2022-01-06
### Highlights
This release focused on fixing bugs, improving compatibility with other tools, and internal code cleanup. There were still some good language additions though, such as let expressions and randsequence statements.

### Language Support
* Added the built-in coverage control methods and predefined macros (thanks @jrudess)
* Added the PLA system tasks (thanks @jrudess)
* Added support for let declarations and let expressions
* Added support for package export directives
* Added full support for union data types, including packed / unpacked / packed tagged / unpacked tagged variants
* Added support for randcase statements
* Added support for randsequence statements
* Added more support for assignment patterns and cleaned up various corner cases and error handling issues. The only thing still not supported for assignment patterns is when they are used as an lvalue.
* Added support for $psprintf as a non-standard alias for $sformatf for compatibility with other tools
* Allow macros to be named after keywords for compatibility with other tools
* Added support for extended foreach array name syntax for compatibility with other tools. For example:
```
int array[2][2];
foreach (array[i]) begin
    foreach (array[i][j]) begin
        array[i][j] = (i + 1) * (j + 1);
    end
end
```
* Allow macro argument substitution inside of escaped identifiers for compatibility with other tools
* Allow macro expanded arguments to insert line continuations when used inside another define directive for compatibility with other tools
* Added support for clocking blocks in modports
* Added support for accessing clocking blocks through virtual interfaces
* Changed rand_mode and constraint_mode to always be considered functions for compatibility with other tools
* Specifying a lifetime on a method prototype has been changed from an error to a warning, to make life easier for legacy codebases

### General Features
* The minimum required cmake version has been bumped to 3.15
* Added a warning for non-blocking assignments used in final blocks (thanks @jrudess)
* Made some general improvements to the SyntaxRewriter APIs
* Instance caching was removed and parameter evaluation was reworked to better support hierarchical names in parameter values in the future. This is not allowed in SystemVerilog but some tools allow it anyway, so this sets the groundwork for eventually supporting it in slang as well.

### Fixes
* Fixed some spurious errors inside of foreach loops within uninstantiated modules
* Fixed error reporting when an invalid base type is used for an enum
* Fixed error reporting when an invalid net initializer is used in a package
* Fixed the check for tasks being called from a constant expression
* Fixed a crash when specparams are given an invalid data type
* Fixed the error message issued when dynamic array range selection bounds are reversed
* Fixed a crash within the handling of unbounded literals being assigned to parameters
* Correctly prevent self-referential parameter initializers
* Correctly allow property and sequence expressions in instance port connections
* Fixed various bugs in parsing covergroups
* Fixed an issue that could cause array iterator methods to evaluate to the wrong value in constant expressions
* Correctly allow event trigger and wait_order statements to target an element of an array of events
* Fixed class member accessibility checking from within randomize inline constraint blocks
* Fixed type checking for unpacked arrays of strings in set membership expressions
* Fixed overriding of inherited enumerands in extended classes
* Fixed class member accessibility checking from out-of-block method default argument expressions
* Fixed parsing of virtual interface properties with class qualifiers
* Added class definitions to JSON AST output
* Fixed a parsing ambiguity in parenthesized event expressions
* Fixed an assertion when macro stringifying an escaped identifier
* Fixed dist constraint type checking
* Fixed implicit macro concatenation with adjacent tokens
* Correctly allow scope randomize arguments to be considered rand variables
* Fixed a bug in SVInt::operator< where both sides are 0 with large bit widths
* Fixed an assertion when data type expressions have erroneous invocation syntax
* Fixed a sequence repetition parsing bug
* Fixed lookup resolving through typedefs that point to an error type
* Fixed binding of special methods on dynamic array (and other) types
* Fixed crash on default value checking for empty assignment patterns
* Fixed checking of allowed types in constraint expressions
* Fixed spurious errors in virtual interface assignment checking
* Correctly disallow out-of-block class methods from having static variable lifetime
* Fixed $sformat argument checking
* Fixed class inheritance issues caused by circular references in base class constructor calls
* Fixed spurious errors in uninstantiated generic classes with unknown base classes
* Improved error reporting for invalid uses of dist expressions
* Correctly handle nested chains of invocable symbols after lookup
* Fixed an off-by-one error in lexer's splitTokens method that led to misparsing some literals
* Fixed a crash when speculatively evaluating an assignment to an expression type that doesn't implement evalLValue
* Fixed various places that could silently fail during constant evaluation
* Fixed an issue where upward names could fail to properly issue all related diagnostics
* Fixed evaluation of body parameters with defaults that depend on local functions

### Extra Thanks
* @Kuree for some build fixes and adding macos to the CI build
* @jesec for some patches to fix the build on non-x86_64 platforms
* @eggman79 for reporting and providing a patch for a memory leak
* @jrudess for reporting many issues and providing helpful test cases
* @chengniansun for running fuzz testing and reporting a bunch of discovered crashes


## [v0.8] - 2021-08-14
### Highlights
Support was added for concurrent assertions, including sequences, properties, and clocking blocks.

### Language Support
* Support for declaring sequences, including all sequence expressions
* Support for declaring properties, including all property expressions
* Support for all concurrent assertion statements
* Initial support for parsing checker declarations
* Support for `#1step` delay values
* Support for clocking blocks and clocking variables
* Support for default and global clocking blocks
* Support for cycle delays
* Support for synchronous drives
* Added the $global_clock system function
* Added the global clocking sampled value system functions
* Support for default disable declarations
* Support for slicing arrays of instances in hierarchical selections
* Initial parsing support for net aliases
* Initial parsing support for package exports
* Initial parsing support for randsequence statements
* Support for assigning unbounded literals to parameters
* Added the $isunbounded system function

### General Features
* Added a specialized diagnostic for when `wire` is misused as a data type
* Added a set of CLI options to control the format of printed diagnostics, such as whether they include line numbers, column numbers, source snippets, etc.
* Added a `--allow-use-before-declare` flag which suppresses errors about names being referenced before their declarations, to ease compatibility with less compliant tools
* `--libdir` will now search for missing packages in addition to missing modules

### Fixes
* Fixed many parsing issues related to assertion expressions
* Fixed the printing of type aliases in diagnostics when they point to virtual interfaces
* Fixed type compatibility checking for virtual interfaces
* Fixed issues with parsing let declarations
* Fixed a bug where predefined integer types that had a signed qualifier added would no longer be treated as a predefined type
* Fixed interconnect net parsing
* Fixes for covergroup parsing
* Fixed a bug related to assigning lookup indices to generate blocks
* Correctly enforce rules about the contents of deferred assertion action blocks
* Correctly disallow system functions with output arguments from being used in invalid contexts
* Fixed the elaboration system tasks to correctly check for constant evaluation errors


## [v0.7] - 2021-04-02
### Highlights
slang now supports enough features to elaborate UVM tests.

### Language Support
* Finished support for upward name lookup
* Support for `$` in queue expressions
* Max bound constraints for queues are now enforced at compile time in constant expressions
* Support for the %l and %v format specifiers
* Support for the parameterized `std::mailbox` class (the dynamic unparameterized form is not yet supported)
* Partial support for virtual interface variables and expressions
* Finished implementing rules for procedural continuous assignments
* The preprocessor now supports concatenating together block comments at macro expansion time, which allows code like this to work:
```SystemVerilog
`define FFSR(__q, __d, __reset_value, __clk, __reset_clk) \
  `ifndef FOOBAR                                          \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/       \
    `endif                                                \
  always_ff @(posedge (__clk)) begin                      \
    __q <= (__reset_clk) ? (__reset_value) : (__d);       \
  end
module m;
  logic q, d, clk, rst;
  `FFSR(q, d, 0, clk, rst)
endmodule
```
* Support for the stochastic analysis system tasks and functions
* Support for the probabilistic distribution system functions
* Support for the $sdf_annotate system task
* Partial support for defparams (does not yet support instance arrays or specific rules about interfaces)
* Support for specparams
* Support for user-defined primitives and instances
* Added parsing support for specify blocks, path declarations, and system timing checks
* Finished support for built-in gate primitives, including type checking of ports and delay expressions
* Finished implementing rules about which kinds of statements and expressions are allowed in function bodies
* Finished implementing rules about which kinds of expressions can reference automatic variables
* Support for null non-ansi module ports
* Finished support for type reference expressions

### General Features
* Added a `--lint-only` flag that does not try to find top-level modules and skips errors related to unknown module instantiations
* Added -Wformat-multibit-strength as a pedantic warning when using %v with multibit nets
* Added -Wenum-range when enum element ranges are not integer literals (as opposed to some constant expression instead)

### Fixes
* `randc` variables are now correctly disallowed in soft constraints
* static constraint blocks are allowed to access instance members
* Fixed detection of whether colors are supported in the calling terminal from the driver
* Reals and strings are now correctly converted to integers when passed as integer display format arguments
* Various rules for continuous assignment lvalues are now correctly enforced
* Delay values specified in continuous assignments are now checked for correctness
* Fixed parsing of function-like macros that have escaped names
* Fixed a bug that allowed multiple unary prefix operators to be placed next to each other in an expression
* Fixed an overly restrictive check on literals that are allowed in enum initializers
* Correctly disallow return statements in fork-join blocks
* Fixed a bug that incorrectly propagated signedness to the rhs of assignment operators
* Fixed a bug that failed to slice connections to output ports across instance arrays
* `ref` arguments are now correctly disallowed in static subroutines
* Fixed expression lookup locations for non-ansi ports that have split I/O declarations and initializer expressions
* Allow real-to-integer conversions by default in repeat statements, $readmem and $writemem tasks
* Fixed a bug that normalized away negative packed array bounds
* Correctly disallow items in generate blocks based on the parent definition kind
* Correctly disallow instances of modules, interfaces, and programs based on the context in which they are instantiated
* Fixed overly permissive parsing rules for package headers
* Correctly allow non-blocking assignments to class properties
* Correctly disallow net initializers in packages
* Fixed default lifetime determination for packages and procedural blocks


## [v0.6] - 2021-01-10
### Highlights
Many large open source SystemVerilog codebases can now be fully elaborated by slang, such as the [black-parrot](https://github.com/black-parrot/black-parrot) project.

### Language Support
* Partial support for `bind` directives
* Support for modports, including enforcing all connection and port access rules
* Full support for DPI import and export directives (except for open array arguments)
* Support for the $assertcontrol family of system tasks
* Support for `iff` conditional event controls
* Support for `wait` statements
* Support for procedural assign / deassign / force / release statements
* Support for intra-assignment repeat event controls
* Implemented remaining support and rules for nets, net types, net delays, and user-defined net types
* Support for `ref` arguments
* Support for all built-in methods on associative arrays
* Support for the built-in `std` package
* Support for the std::process class
* Support for the std::semaphore class
* Enforce all rules around optional parenthesis when invoking subroutines
* Support for `with` array iterator expressions, including in constant expressions
* Added the sum, product, sort, rsort, reverse, shuffle, min, max, unique, unique_index built-in array methods
* Added the find, find_index, find_first, find_first_index, find_last, find_last_index built-in array methods
* Support for `rand` and `randc` class properties
* Added the randomize, pre_randomize, post_randomize, srandom, get_randstate, set_randstate built-in class methods
* Added the $urandom_range system function
* Added the rand_mode and constraint_mode built-in methods on classes and properties
* Full support for class constraint declarations and constraint blocks, including all class qualifiers and name lookup rules
* Full support for inline constraint blocks via `with` expressions on `randomize` calls, including `local::` name lookup
* Support for left justifying integers when formatting with $sformatf

### General Features
* Added a -G command line option which can override top-level module parameter values
* Added a --ast-json-scope option which controls which scopes are dumped to JSON
* Added -Wwidth-expand and -Wwidth-trunc (both off by default) which warn about implicit integral conversions that change size
* Added -Wimplicit-conv (on by default) which warns about implicit conversions between different structs / unions / enums
* Did a cleanup pass on warning text and grouping into categories. The default set of warnings should now consist only of warnings that have a very high likelihood of being a real problem. The -Wextra group is recommended but not enabled by default. -Wconversion is a new group that includes all implicit conversion-related warnings.
* Added a --ignore-unknown-modules flag which suppresses errors for instantiations of unknown modules
* The driver tool now prints errors to stderr instead of stdout
* Added --libdir and --libext flags to allow automatically searching for files to include in the build when encountering unknown modules
* Added a -v flag to include source files that are treated as "libraries", meaning modules in them are not automatically instantiated

### Fixes
* Fixed many issues related to spurious semantic errors reported inside uninstantiated modules
* Fixed traversal of statement bodies via the ASTVisitor helper class
* Fixed incorrect errors reported for non-ANSI ports with separate I/O and type declarations
* Fixed many issues related to method prototype declarations
* Unpacked arrays now correctly support up to 2^31 elements
* Implicitly typed parameters that are assigned string literals are themselves treated as string literals in other expressions
* Fixed accidental truncation of bits that was occurring when connecting array ports across interface instance array instantiations
* Fixed type checking for compound assignment operators
* Fixed lookup of class names in packages
* Fixed many issues with class inheritance
* Fixed crash when visiting generic class specializations leads to more specializations being created
* Fixed merging of port types across separate I/O and type declarations, including in subroutine bodies
* Fixed `foreach` loops to work with strings and predefined integer types
* Fixed `foreach` loops over class properties
* Don't report an error when `void` casting a system subroutine that can be both a task and a function
* Fixed a check for variable initializers that reference themselves in their own declaration
* Fixed lookup of subroutines when invoking them without parenthesis
* Port connections were missing in AST JSON output
* Fixed lookup of event objects in various statements
* Fixed visibility checks for members of generic classes
* Trailing '%' symbols in format strings are now a warning instead of an error


## [v0.5] - 2020-10-26
### Highlights
This release contains full elaboration support for classes, including generic classes, virtual classes, and interface classes.

### Language Support
* Added full support for classes and all related features
* Added support for bitstream casting (thanks to @thingkingland )
* Added support for streaming operator expressions (thanks to @thingkingland )
* The parser now enforces language rules about which kinds of members are allowed in certain scopes
* Added support for elaboration system tasks ($warning, $error, etc)
* Added support for the $cast system task
* Added support for chandles
* Added support for events and event trigger statements
* Added support for the wait_order statement
* Finished remaining string and string-literal expressions and conversions

### General Features
* Added -Wunused-def (off by default) which warns about unused module/interface/program definitions
* Added -Wno-top which warns if no top-level modules are found in a design
* Added -Wtask-ignored for system tasks that get skipped during constant evaluation
* Added -Wunsized-concat which warns for unsized integers used in concatenations
* Added a --top option which can be used to manually specify the top-level modules in a design
* The slang driver now reports the discovered top-level modules when elaborating unless --quiet is passed

### Fixes
* slang will no longer try to automatically instantiate unused modules that have interface ports
* Cleaned up type checking that is performed in uninstantiated modules
* Fixed the build to work for macOS (thanks to @thingkingland )
* Fixed corner cases for assignment of unpacked arrays (thanks to @thingkingland )
* Fixed a bug that prevented empty port connections from working correctly
* Fixed a bug that prevented empty parameter assignments from working correctly
* Fixed bugs related to constant evaluation involving mixed signedness of expressions (thanks to @thingkingland )
* Fixed constant evaluation of shift operators with negative or unknown amounts (thanks to @thingkingland )
* Fixed detection of whether statements are in a loop when those statements are in a nested level of block hierarchy
* Fixed a preprocessor bug related to macro concatenation


## [v0.4] - 2020-08-16
### Highlights
This release contains a lot of internal refactoring and cleanup, with the goals of correctly handling all corner cases as well as dramatically speeding up compilation time -- some projects and workloads may see up to a 10x speedup.

### Language Support
* Support for intra-assignment timing controls
* Full support for dynamic arrays in type checking and constant expressions
* Full support for associative arrays in type checking and constant expressions
* Partial support for queues in type checking and constant expressions (still missing expressions involving the '$' magic value)
* Added $dimensions and $unpacked_dimensions system functions
* Added $printtimescale, $timeformat, and $system functions
* Added $ferror, $fgets, $fscanf, $sscanf, and $fread system functions
* Support for disable statements
* Support for unpacked array concatenations
* Support for min:typ:max expressions
* Support for disable-fork and wait-fork statements
* String literals can now correctly be implicitly assigned to unpacked arrays of bytes (thanks to @thingkingland )

### General Features
* Reworked how definitions and instances are represented, both to make the code clearer as well as to allow caching of identical instances.
* Timing controls are now included in AST->JSON serialization (thanks to @Kuree ).
* Added initial support for generating simulation code for designs using LLVM. There's enough support here to simulate a basic "Hello World" example but not much else.
* To facilitate code generation, a mid-level IR representation was added to sit between the AST and LLVM. In the future this could grow to be useful to other consumers as well.
* Went through and removed experimental code analysis services from the repository and ported the CI build to GitHub actions, fixing the automated release and deployment pipeline in the process.
* Split slang into several component libraries to make it easier to link in only subsets of functionality.
* Added a bunch more API reference documentation.
* The remaining 3rd party dependencies have been vendored into the repo under the external/ folder. The conan package manager has been removed from the build process.

### Fixes
* Fixed a bug where stringifying certain integer literals could produce garbage results.
* Improved parser error recovery in more scenarios.
* Fixed several crashes found by fuzz testing.
* Empty concatenations now correctly report an error.
* Fixed a faulty error reported when range-selecting a single bit from a big-endian vector.
* Fixed the type that is inferred for implicitly typed parameters.
* Rewrote lvalue handling in constant expressions to fix several corner cases.
* Fixed a crash in the preprocessor involving a rare case of macro replacing a token that then becomes another macro.
* Fixed parsing of cycle delays.
* Fixed ANSI color output on Windows terminals.
* Fixed variable lifetimes of task arguments.
* Packed dimensions on enum declarations were previously being ignored.
* Added additional error checking for various array creation rules.
* Fixed an infinite loop in the parser caused by unsupported statements (thanks to @thingkingland ).
* Fixed a bunch of issues with parsing new expressions.
* Fixed a bunch of issues with parsing clocking blocks.
* The error reported for non-standard character escape codes has been downgraded to a warning.


## [v0.3] - 2020-03-24
### Highlights
As of this release the preprocessor is 100% complete. This does not mean bug free (though I hope so!) but rather that all known features are finished, all known bugs are fixed, and there is 100% coverage in unit tests.

### Language Support
* Initial support for gate instantiations in the parser and AST
* Tightened a bunch of parser rules for things like variable modifiers
* Support parsing strength and delay modifiers in continuous assignments
* Support creating implicit nets in all places allowed by the LRM
* Full support for pragma directives in the preprocessor
* $typename should now return the correct result for all types, as mandated by the LRM
* Support for the type() operator in all places type references are allowed
* Support for slicing packed and unpacked arrays across module array instantiations
* Implement all rules related to variable lifetimes (static vs automatic)
* Correctly prevent assignments to constants, nonblocking assignments to automatic variables
* Support const'() casts
* Support time literals, including all of the scaling and rounding rules

### General Features
* Lots of work was done on the documentation, CI builds, and the website. Check it out!
* I removed most dependencies on 3rd party libraries that didn't do exactly what I wanted. This slims down the dependency tree and improved performance.
* A bunch of improvements were made to the AST->JSON serialization (thanks @Kuree )
* Printing of types in diagnostics was improved
* Added a general system for correcting typos. For example:
```SystemVerilog
module m;
    int someInt;
    int foo = someIn;
endmodule
```
```
source:3:15: error: use of undeclared identifier 'someIn'; did you mean 'someInt'?
    int foo = someIn;
              ^~~~~~
source:2:9: note: declared here
    int someInt;
        ^
```

### Fixes
* Lots of fixes to error recovery and error reporting in various cases
* Struct members that required looking up type names was previously broken and has now been fixed
* Fixed the check applied to enum initializers with unknown bits for 2-state base types
* Port connections were previously not being type checked; that has been fixed
* Fixed the result type of unary bitwise-not expressions


## [v0.2] - 2020-01-20
This release fills in a bunch of missing holes and corner cases and cleans up a bunch of bugs. The first beginnings of a more structured release process and documentation system are in place.

This is the first release as of which feature support is tracked in the documentation.


## [v0.1] - 2019-12-02
This is the first release of slang that is somewhat useful. The library supports lexing, preprocessing, parsing, type checking, and elaboration for a good portion of the language. The slang tool can be run on medium to large codebases and print out useful diagnostics.

There's still plenty of work to do but it seemed like a good idea to take a checkpoint.
