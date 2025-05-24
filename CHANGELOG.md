# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]
### Language Support
### Potentially Breaking Changes
### New Features
### Improvements
### Fixes


## [v8.1] - 2025-05-23
### Fixes
* The restriction on interface instances targeted by defparams not being allowed with virtual interfaces was also erroneously applied to interface port connections
* Fixed a null pointer crash in slang-tidy (thanks to @rhanqtl)
* Fixed a bug that could cause infinite recursion when instantiating bind targets that force elaboration due to wildcard package imports
* Fixed the handling of disable region directives declared in block comments (as opposed to single line comments which were working fine)
* Fixed a spurious error when cycle delays are used in an uninstantiated context that does not have default clocking specified
* Fixed an issue with how checker formal ports are looked up from within checker instances
* Fixed ICE with conditional statements that have pattern matching along with a named statement block
* Recursive typedef declarations now properly report an error instead of crashing
* Fixed several issues that led to invalid builds on Linux with LTO enabled
* Fixed a case where no diagnostic would be issued when incorrectly referring to an instance array element from within an expression
* Fixed SyntaxPrinter printing of directives that have skipped leading trivia
* Fixed rewiring of interface array port connections with opposite declared range directions
* Fixed a bug in the constant evaluation of division between two positive signed integers; the sign flag was lost and the result was always treated as unsigned
* Fixed JSON serialization of definition symbol attributes
* The `--obfuscate-ids` option has been fixed to not generate invalid SystemVerilog names that start with a digit (thanks to @Sustrak)
* Fixed slang-tidy's module instantiation prefix check to use the correct diagnostic (thanks to @corco)
* Fixed $static_asserts triggering in uninstantiated contexts (thanks to @AndrewNolte)
* Fixed `--allow-use-before-declare` to apply to wildcard port connection expressions


## [v8.0] - 2025-02-05
### Language Support
* Disallow access to protected members from class scoped randomize constraint blocks -- the LRM is unclear about this but other tools seem to have decided this way made the most sense
* Added a check that net aliases aren't duplicated, and that nets don't alias to themselves, as mandated by the LRM (thanks to @likeamahoney)
* Implemented remaining rules for virtual interfaces:
  * Virtual interfaces can't have hierarchical references to objects outside the interface
  * Virtual interfaces can't have interface ports
  * Instances assigned to a virtual interface can't have an instance configuration rule applied to them

### Potentially Breaking Changes
* The minimum supported Xcode version is now 16 and the minimum supported Clang version is now 17 (to allow cleaning up workarounds for various bugs)

### New Features
* Added [-Wudp-coverage](https://sv-lang.com/warning-ref.html#udp-coverage) which warns about edge-sensitive user-defined primitives that don't specify an output state for all edges of all inputs (thanks to @likeamahoney)
* Added [-Wpacked-array-conv](https://sv-lang.com/warning-ref.html#packed-array-conv) which warns for conversions between different multidimensional packed array types even if their overall bit width is the same
* Added the [-Wparentheses](https://sv-lang.com/warning-ref.html#parentheses) warning group for diagnosing common precedence-related syntactical errors, which includes the following new warnings: [-Wbitwise-rel-precedence](https://sv-lang.com/warning-ref.html#bitwise-rel-precedence), [-Warith-in-shift](https://sv-lang.com/warning-ref.html#arith-in-shift), [-Wlogical-not-parentheses](https://sv-lang.com/warning-ref.html#logical-not-parentheses), [-Wbitwise-op-parentheses](https://sv-lang.com/warning-ref.html#bitwise-op-parentheses), [-Wlogical-op-parentheses](https://sv-lang.com/warning-ref.html#logical-op-parentheses), [-Wconditional-precedence](https://sv-lang.com/warning-ref.html#conditional-precedence), [-Wconsecutive-comparison](https://sv-lang.com/warning-ref.html#consecutive-comparison)
* Added [-Wcase-type](https://sv-lang.com/warning-ref.html#case-type) to warn about case statements with mismatching types in their item expressions
* Added [-Wcase-default](https://sv-lang.com/warning-ref.html#case-default) which warns about case statements that don't include a `default` label
* Added [-Wcase-outside-range](https://sv-lang.com/warning-ref.html#case-outside-range) which warns for case items that can never be matched because they are outside the range of the case condition expression
* Added [-Wcase-enum](https://sv-lang.com/warning-ref.html#case-enum) and [-Wcase-enum-explicit](https://sv-lang.com/warning-ref.html#case-enum-explicit) which warns about enum values that are missing from a case statement (with and without the presence of a `default` label, respectively)
* Added [-Wcase-dup](https://sv-lang.com/warning-ref.html#case-dup) which warns about duplicate item expressions in a case statement
* Added [-Wcase-overlap](https://sv-lang.com/warning-ref.html#case-overlap) which warns about overlapping case items (due to wildcard bits)
* Added [-Wcase-not-wildcard](https://sv-lang.com/warning-ref.html#case-not-wildcard) and [-Wcasez-with-x](https://sv-lang.com/warning-ref.html#casez-with-x) which warn about potentially misleading wildcard bits in non-wildcard case statements
* Added initial support for instance caching, which skips elaborating identical module instances to speed up elaboration. This is currently hidden behind the `--disable-instance-caching` command line flag because when turned on not all multi-driven errors are properly issued. Once all issues have been worked out the feature will be turned on by default.
* Added the ability to output diagnostics to JSON instead of (or in addition to) plain text
* Added `--translate-off-format` which allows specifying comment directives that should act as skipped regions (for example, `// pragma translate_off` and `// pragma translate_on`)
* slang warnings can now be turned on and off within source code using `// slang lint_off` style comment directives
* Added `--ast-json-detailed-types` to include detailed type information in AST JSON output
* slang-tidy gained a `clkNameRegexString` option to control how clocks are named (thanks to @spomatasmd)

### Improvements
* Made -Wuseless-cast a bit less noisy -- it now does not warn about expressions involving genvars or cases where types are matching but one or the other has a different typedef alias name
* -Wsign-compare no longer warns about expressions involving genvars
* -Wvector-overflow no longer warns about signed literals with binary, octal, or hex bases that place a bit in the MSB
* Made some build tweaks to support hermetic builds (thanks to @cc10512)
* Added support for unions to slang-reflect (thanks to @Sustrak)
* Changed the error issued for sequences that can never be matched to be a warning instead (-Wseq-no-match) and added additional context to the diagnostic message
* Made minor tweaks to improve defparam and bind resolution performance
* -Wsign-conversion will no longer warn for certain system functions that have a return type of `int` but in practice only return a single bit result
* Made some minor improvements to parser error recovery when struct definitions are missing a closing brace
* Inline genvars declared in generate loops are now included in the generate loop's members list when serializing the AST
* The pyslang packaging build is now done in this repo instead of a separate downstream repo (thanks to @parker-research)
* pyslang wheels now include support for arm64 (thanks to @gadfort)
* Documentation now includes the READMEs for the various ancillary slang tools
* Added stub generation to the Python distribution (thanks to @parker-research)

### Fixes
* Fixed a bug with constant evaluation of left-hand side assignment patterns that require implicit conversions to be applied
* Fixed the locations returned by Trivia::getExplicitLocation for nested trivia involving directives (thanks to @povik)
* Fixed checking of illegal property negation operator when used within recursive property instantiations (thanks to @likeamahoney)
* Fixed a bug with serializing UninstantiatedDef AST nodes that use implicit named port connections
* Fixed a crash when checking duplicate drivers in assignments to invalid ranges of a vector
* Correctly allow unpacked unions to be used in equality and conditional expressions
* Fixed spurious warnings inside an unused generic class that instantiates the default specialization of itself
* Fixed Python bindings build to work with Python 3.13 (thanks to @vowstar)
* Fixed a spurious error when assigning the empty queue to an unresolved / unknown typed variable
* Correctly disallow override specifiers on class constructor declarations
* Correctly report an error for unbased unsized literals that use a `?` instead of a `z` character for high impedance
* Fixed handling of connections of interface arrays to ports with different declared dimensions
* Fixed a bug in constant evaluation of packed struct member access
* Correctly disallow select expressions of a parenthesized subexpression
* Fixed a bug where some type declarations in two modules with different parameter values could be erroneously considered equivalent to each other (thanks to @povik)
* Correctly disallow derived class virtual methods from declaring a different visibility level from their base class method
* Reworked how enum types are implemented to fix various issues related to enum values declared inside subexpressions from being visible to their surrounding scopes
* Fixed several issues related to enum value initializers that try to refer to themselves or other enum values
* Fixed a parser crash when an invalid class override specifier is at the very end of a file
* Fixed a potentially unbounded loop when resolving a specific case of invalid bind directives
* Fixed bad diagnostic output related to instantiating properties with missing formal argument names
* Fixed several minor issues with the Python bindings (thanks to @parker-research)
* Fixed bugs with pattern variables not being visible in certain scopes where they otherwise should have been
* Pattern variables are now properly usable from static variable initializer expressions
* $sformat in constant expressions now works properly with %p specifiers
* Fixed -Wwidth-expand to apply to conditional expressions
* Fixed \[\*\] and ##\[\*\] sequence repetitions to start from 0 instead of 1 (thanks to @georgerennie)
* Fixed a case where nested attributes were not properly diagnosed (thanks to @likeamahoney)
* Fixed type resolution for expressions involving static casts; previously the operand of the cast was considered self determined, but now the type of the cast is correctly propagated to the operand
* Fixed a bug in SyntaxNode::isEquivalentTo which would cause it to sometimes return the wrong result
* Fixed the direction of argument binding for n-output gate terminals


## [v7.0] - 2024-09-26
### Language Support
* Select expressions of packed arrays now always return an unsigned type, as mandated by the LRM
* Clocking skew delays now properly require a constant value
* Enforce that static methods can't have override specifiers
* The error for invalid state-dependent path conditions in specify blocks can now be downgraded with -Wspecify-condition-expr for compatibility with other tools
* Added support for the optional system tasks and functions from Annex D in the LRM: `$countdrivers`, `$list`, `$input`, `$key`, `$nokey`, `$reset`, `$reset_count`, `$reset_value`, `$save`, `$incsave`, `$restart`, `$scope`, `$scale`, `$showscopes`, `$showvars`, `$sreadmemb`, `$sreadmemh`, `$getpattern`
* Added support for the optional compiler directives from Annex E in the LRM: `` `default_decay_time ``, `` `default_trireg_strength ``, `` `delay_mode_distributed ``, `` `delay_mode_path ``, `` `delay_mode_unit ``, `` `delay_mode_zero ``
* Rules about nondegeneracy of sequences and properties are now enforced (thanks to @likeamahoney)
* Special case rules about how name resolution works in bind directives are now enforced
* Changed the definition of "simple types" to include `string` to allow using it as a target for assignment pattern fields (thanks to @likeamahoney)
* Rules for inconsistent net types connected via an implicit named port connection are now enforced (thanks to @likeamahoney)
#### Clarifications in IEEE 1800-2023
* Assertion clocking events can't reference automatic variables
* The `.*` token sequence is actually two separate tokens that can be separated by whitespace
* Functions in constraints cannot have `inout` arguments
* Constraint subexpression can be of any type as long as their final expression type is numeric and they don't reference random variables
* The argument to `$isunbounded` must be a parameter name (only enforced as a pedantic warning in slang)
* Edge-sensitive paths in specify blocks can specify an edge keyword without also including a data source expression
* Only bidirectional switches allow connections to nets with user-defined net types (other primitives do not)
#### New Features in IEEE 1800-2023
* Constraint expressions and random variables can have `real` types
* `dist` expressions can have a `default` specifier
* `dist` expressions can have `real` types
* solve-before constraints can specify array.size() as well as regular random variables
* disable soft constraints can target array.size()
* Constraint blocks can have override specifiers (initial / extends / final)
* Covergroups can inherit from covergroups in parent classes
* Coverpoints can have `real` types
* Covergroups have new options: `cross_retain_auto_bins` and `real_interval`
* New system functions `$timeunit`, `$timeprecision`, and `$stacktrace`

### General Features
* Added [-Wunsigned-arith-shift](https://sv-lang.com/warning-ref.html#unsigned-arith-shift) which warns about suspicious arithmetic right shifts of unsigned types
* Added [-Wstatic-init-order](https://sv-lang.com/warning-ref.html#static-init-order) and [-Wstatic-init-value](https://sv-lang.com/warning-ref.html#static-init-value) which warn about static initializers that depend on uninitialized values or an undefined order of other static initializers
* Added [-Wfloat-int-conv](https://sv-lang.com/warning-ref.html#float-int-conv) and [-Wint-float-conv](https://sv-lang.com/warning-ref.html#int-float-conv) which warn about implicit conversions between floating point and integer types
* Added [-Wfloat-narrow](https://sv-lang.com/warning-ref.html#float-narrow) and [-Wfloat-widen](https://sv-lang.com/warning-ref.html#float-widen) which warn about implicit conversions between floating point types of differing widths
* Added [-Wunused-import](https://sv-lang.com/warning-ref.html#unused-import) and [-Wunused-wildcard-import](https://sv-lang.com/warning-ref.html#unused-wildcard-import) which warn about unused import directives
* Added [-Warith-op-mismatch](https://sv-lang.com/warning-ref.html#arith-op-mismatch), [-Wbitwise-op-mismatch](https://sv-lang.com/warning-ref.html#bitwise-op-mismatch), [-Wcomparison-mismatch](https://sv-lang.com/warning-ref.html#comparison-mismatch), and [-Wsign-compare](https://sv-lang.com/warning-ref.html#sign-compare) which all warn about different cases of mismatched types in binary expressions
* slang-netlist has experimental support for detecting combinatorial loops (thanks to @udif)
* Added `--allow-merging-ansi-ports` (included in "vcs" compat mode) which allows non-standard behavior in which ANSI module ports can duplicate net and variables declared within the module
* Added `--ast-json-source-info` which includes source line information when dumping an AST to JSON (thanks to @KennethDRoe)
* Added `--enable-legacy-protect` which enables support for nonstandard / legacy protected envelopes: Verilog-XL style `` `protect `` directives and Verilog-A style `// pragma protect` comments

### Improvements
* Default value expressions for parameters that are overridden are now checked for basic correctness and other parameters they reference will not warn for being "unused"
* Made several minor improvements to the locations reported for propagated type conversion warnings
* Sped up `Compilation` object construction by reorganizing how system subroutines are created and registered
* Improved the parser error reported when encountering an extraneous end delimiter in a member list
* Various fixes and improvements were made to slang-netlist (thanks to @jameshanlon, @udif)
* Added options to slang-tidy to better control what gets output (thanks to @Sustrak)
* Added a bunch of new checks to slang-tidy (thanks to @JoelSole-Semidyn)
* Improved handling of source files that contain non-UTF8 comments (thanks to @udif)
* Fixed and improved various parts of the SyntaxRewriter API (thanks to @sgizler)

### Fixes
* Fixed several AST serialization methods (thanks to @tdp2110, @likeamahoney, @Kitaev2003, @cyuzuzo-j)
* Fixed the return type of DPI import tasks
* Fixed a bug that caused some `inout` ports to warn as "unused"
* Fixed the checking of the `extends` override specifier when the containing class has no base class
* Fixed a case where bracketed delay expressions in sequence concatenations were not checked for correctness
* Fixed the type of the iterators used in with-expressions for covergroup bins
* Fixed a bug that sometimes prevented printing the correct scope for type alias names in diagnostic messages
* Fixed the hierarchical path string created for symbols inside of unnamed generate blocks (thanks to @povik)
* Fixed spurious errors that could occur when using generic class instantiations inside uninstantiated generate blocks
* Correctly disallow passing expressions of `void` type to format style system functions (thanks to @tdp2110)
* Fixed a bug where parameters that referred to themselves via hierarchical reference would cause a crash instead of reporting a diagnostic
* Fixed `PATHPULSE$` specparam initializers to allow providing only one value instead of requiring two (thanks to @likeamahoney)
* Fixed PLA tasks to accept concatenation expressions as arguments without reporting an error about the direction of the argument bounds (thanks to @likeamahoney)
* Fixed a bug that could cause spurious errors in uninstantiated generic class definitions
* Fixed the Symbol::getHierarchicalPath API to round-trip correctly
* Fixed JSON serialization of integers to round-trip correctly
* Fixed a bug in resolving defparam values inside of generate loops
* Fixed checking of event arguments in system timing check functions
* Fixed checking of deferred assertion function calls (thanks to @likeamahoney)
* Correctly issue an error if a sequence or property has a formal argument with the same name as a local variable declaration (thanks to @likeamahoney)
* Fixed a case of recursive property instantiation that was incorrectly disallowed (thanks to @likeamahoney)
* Fixed bugs in checking for overlapping user-defined primitive table rows (thanks to @likeamahoney)
* Fixed infinite loops in the parser when encountering constraint blocks with certain kinds of invalid tokens in them (thanks to @likeamahoney)
* Fixed errors in assigning to select expressions involving members of virtual interfaces (thanks to @micron-ian)


## [v6.0] - 2024-04-21
### Language Support
* Added `--allow-bare-value-param-assigment` (included in 'vcs' compat mode) to allow a non-standard module instantiation syntax where a single parameter value can be supplied without including parentheses
* Added `--allow-self-determined-stream-concat` (included in 'vcs' compat mode) to allow the use of streaming concatenation expressions in self-determined contexts (instead of just in assignments)
* Added `--allow-multi-driven-locals` (included in 'vcs' compat mode) to allow subroutine local variables to be driven by multiple always_ff / always_comb blocks
* Added full support for SystemVerilog libraries and configurations
* Added support for equality comparisons between virtual interfaces and actual interface instances (thanks to @likeamahoney)
* Ref args are now correctly disallowed in fork-join_any and join_none blocks
* Wildcard port connections now correctly avoid importing new symbols into a scope via wildcard imports
* Added support for referencing interface instances in unpacked array concatenations involving virtual interface arrays
#### Clarifications in IEEE 1800-2023
* Unsized integer literals can be any bit width, not just capped at 32 bits.
* Unpacked unions are allowed as net types
* Time literals should be scaled but *not* rounded to the current time precision
* Multiline block comments are allowed in macro definitions
* Set membership operations (case statements, inside operator) always allow unbounded literals
* Unbounded literals can only be assigned to parameters with simple bit vector types
* $cast arguments don't need to be singular at compile time
* Checking for multi-driven variables in subroutines invoked from always_comb/_latch/_ff doesn't apply to tasks, only functions
* Non-blocking assignments to elements of dynamic arrays are not allowed
* Static casts are assignment-like contexts
* Tagged union expressions must be primaries only (binary expressions are not allowed)
* Severity system tasks should work in constant functions (and behave as elaboration-time tasks)
#### New Features in IEEE 1800-2023
* Triple quoted (multiline) string literals
* Macro stringification with triple quoted strings
* Type parameters and the type() operator can now refer to incomplete forward typedefs
* Type parameters can now specify a type restriction just like forward typedefs
* The `timescale directive is disallowed inside design elements
* Boolean expressions in conditional directives (ifdef, ifndef)
* Function call expressions can be chained (slang already supported this but several issues related to it were fixed)
* `type(this)` is now allowed in static contexts within class declarations
* Soft packed unions
* The `index` method of array iterators can be renamed via an argument to the method call
* Unpacked arrays have a built-in `map` method
* Classes can be declared `final`
* Class constructor argument lists and `extends` argument lists can be declared `default`
* Class methods can be declared `initial`, `extends`, and `final`
* Added the `weak_reference` built-in class
* Interface classes can be declared within other classes
* The built-in `process` class is declared `final`
* Value ranges gain new absolute / relative tolerance operators
* `ref static` subroutine arguments

### General Features
* Added [-Wmultibit-edge](https://sv-lang.com/warning-ref.html#multibit-edge) (on by default) to warn about clock edge triggers on multibit expressions
* Added [-Wint-bool-conv](https://sv-lang.com/warning-ref.html#int-bool-conv) and [-Wfloat-bool-conv](https://sv-lang.com/warning-ref.html#float-bool-conv) to warn about multibit integer and floating point expressions used in a boolean context
* Added [-Wuseless-cast](https://sv-lang.com/warning-ref.html#useless-cast) to warn about explicit casts to the same type as the underlying expression
* Added [-Wunknown-sys-name](https://sv-lang.com/warning-ref.html#unknown-sys-name) to allow downgrading the error that occurs when referencing an unknown system task or function
* Added [compilation unit listings](https://sv-lang.com/user-manual.html#unit-listing) to allow fine grained control over how sources are parsed into separate compilation units (including separating macro defines and include directories on a per-unit basis)
* Added `--defaultLibName` to control the name of the default source library
* Added `--std` to choose which version of the LRM slang should conform to. By default this is "1800-2017" but can be set to "1800-2023" to enable new features added in the recently published update to the SystemVerilog LRM.
* Added a new experimental tool, slang-hier, that prints elaborated instances in a design (thanks to @udif)

### Improvements
* `--cmd-ignore` and `--cmd-rename` now also work with options that include a value via an equals expression
* Information about module/interface/program definitions are now included in AST JSON output
* slang-reflect has been improved to support reflecting more complex types for local parameters (thanks to @Sustrak)
* Rewrote analysis of user-defined primitive tables to be much more efficient; previously primitives with large numbers of inputs could take a very long time to analyze
* Command line defines now take precedence over defines in Verilog source files, which matches the behavior of other tools (thanks to @udif)
* -Wvector-overflow has been improved to not warn when forming minimum negative integer literals
* Backslashes at the end of lines in command files are now ignored instead of causing errors (thanks to @udif)

### Fixes
* Fixed several crashes in slang-tidy (thanks to @likeamahoney)
* Fixed a bug where a missing `endif directive didn't always cause an error to be issued
* Fixed the use of the `this` handle in non-static class property initializer expressions
* Fixed a bug where use of the unqualified `randomize` would sometimes find std::randomize when it should have found a class-local randomize method
* Fixed several spurious lexer errors when otherwise invalid tokens are used inside stringified macro expansion
* Fixed a crash in the Python SyntaxVisitor bindings
* Correctly allow instance paths to be used in assert control system function arguments
* Fixed a bug where multi-driver checks for called subroutines didn't apply when one of the source procedures was a plain `always` block
* Fixed bug in parsing empty action blocks for sequences and properties
* Fixed the Python bindings for `Type::isBitstreamType`
* Fixed a crash when calling `getResolutionFunction` on built-in net types
* Fixed a bug in the checking of forward typedef type restrictions
* Fixed the end spacing of stringified macro expansions
* Fixed a macro expansion corner case where an escaped identifier that ends in a backslash was not considered as a line continuation for the macro body
* Fixed several cases where invalid syntax could lead to follow on errors with malformed messages
* Fixed several crashes related to corrupted source files containing embedded null characters or invalid UTF8 sequences
* Fixed a crash that could occur when a source file ended in an invalid hex escape inside an unterminated string literal
* Fixed an infinite loop when parsing a malformed list of terminals in a primitive declaration
* Fixed an infinite loop caused by malformed recursive checker instantiations
* Fixed an infinite loop when parsing case statements with malformed pattern items
* Added checking for several missing invalid corner cases in user-defined primitive declarations
* Fixed the propagation of unbounded literals through parameters used in expressions
* Fixed handling of nested modules to be properly independent of each other when there are multiple instances of their parent module
* Fixed handling of bind directives that target nested modules
* Fixed handling of bind directives that appear in uninstantiated generate blocks
* Fixed handling of include files that don't contain a newline character (thanks to @ihathbeer)
* Fixed handling of classes that declare a member named "\new" with an escaped identifier
* chandles are properly allowed in non-edge event expressions
* Correctly disallow `wait fork` and `expect` in functions and final blocks
* Fixed bug in computing bounds for assignments to slices of unpacked arrays
* Fixed macro argument parsing when there are `(*` and `*)` tokens in them
* Fixed a bug in `SVInt::operator<` when comparing the smallest possible negative integer (thanks to @Krym4s)
* Correctly allow non-blocking assignments with a timing delay to be used in `always_ff` blocks (thanks to @udif)
* Fixed checking of overlapping primitive table rows when the '-' output character is used (thanks to @udif)
* Fixed checking for which kinds of functions are allowed in deferred assertion actions and sequence match items
* Fixed a couple of places where range selects were not properly checked for overflow
* Fixed sorting of diagnostics when buffers are loaded in non-deterministic order
* Added error handling for packages that try to import themselves
* Type references and assignments of type `void` are now correctly disallowed
* Fixed several bugs in slang-netlist (thanks to @jameshanlon)
* Fixed `--allow-toplevel-iface-ports` when used with interface arrays


## [v5.0] - 2023-12-26
### Language Support
* Added support for specifying a modport when connecting an interface array port
* Implicitly typed parameters that have range specifications are now considered assignment-like contexts (this behavior is not specified in the LRM but more intuitively matches user expectations)
* Added support for using assignment patterns as lvalues (which finally finishes full support for assignment patterns)
* Added partial support for SystemVerilog configurations. Support is incomplete and may be buggy.
* Index selects after range/part selects are now disallowed, to conform to the LRM as well as match the behavior of other tools
* An error is now issued for interface ports that connect hierarchically through a generate or instance array, as mandated by the LRM
* An error is now issued for generic interface ports that are connected via a wildcard connection, as mandated by the LRM
* Rules about where classes with private members are allowed to be used in bitstream casts are now enforced
* Relaxed requirement that DPI import declarations have an explicit return type to match behavior of other tools
* Added `-Wdpi-pure-task` to allow downgrading the error that DPI import tasks cannot be marked `pure`
* Added `--relax-string-conversions` (included in "vcs" compat mode) to allow strings to implicitly convert to integers
* Added `--allow-recursive-implicit-call` to allow implicit call expressions to be recursive function calls for compatibility with other tools

### General Features
* Minimum required compiler versions have been bumped to GCC 11, clang 16, and Xcode 15 (should be the last bump for a while)
* Minimum required cmake version has been bumped to 3.20
* Added `--allow-toplevel-iface-ports` to allow top level modules that have interface ports
* Added [-Wconstant-conversion](https://sv-lang.com/warning-ref.html#constant-conversion) which warns about conversions inside constant expressions that lose information
* Added [-Wsign-conversion](https://sv-lang.com/warning-ref.html#sign-conversion) which warns about implicit integral conversions that change sign
* Added a `-L` option to control the default [source library](https://sv-lang.com/user-manual.html#source-libraries) search order
* The `--diag-hierarchy` option now takes a parameter of "always", "never", or "auto" to allow forcing or hiding instance paths in diagnostics

### Improvements
* Made several improvements to -Wimplicit-conv to make it less noisy
* Cleaned up internal code related to wide character support for Windows. slang now relies on the relatively new utf-8 code page support in Windows; this does mean that Unicode paths will now only be handled correctly on or after Windows Version 1903 (May 2019 Update).
* The maximum size of a type has been increased to 2^31 bytes (which matches VCS)
* The `--suppress-warnings` feature has been optimized to not perform unnecessary filesystem operations

### Fixes
* Fixed a case where -Wimplicit-conv would not be issued for mismatching struct types
* Fixed a crash when $static_assert condition is parenthesized
* Fixed the count of compilation errors reported when using -Werror along with `--suppress-warnings`
* Fixed -Wvector-overflow to work correctly with signed literals
* Fixed the type infered for parameters that are assigned vector literals larger than 32-bits wide
* SystemVerilog class types (and other types that contain them) are now limited to the max object size supported by slang (the same limit for structs and arrays that was already present)
* Fixed a few places where large types or expressions could result in internal overflow of variables tracking their sizes, which could cause crashes or other strange behavior. Now a proper error is issued.
* A proper error is now issued for duplicate local variables inside of properties and sequences
* Fixed a crash when trying to connect an extern subroutine implementation to an interface array port
* Fixed a spurious error about signals being multi-driven from uninstantiated generate blocks
* Fixed a spurious error when streaming concatenations are used in port connections of uninstantiated modules
* An appropriate parse error is now issued for generate blocks that are missing a body
* Fixed a crash when classes with cycles in their members are used in a cast expression
* Fixed a bug in parsing parameter ports when their type was explicitly package scoped and the parameter keyword was elided
* Fixed a bug in the slang driver that prevented showing instance paths in diagnostics
* An error is now issued for invalid use of the unique and priority keywords in `else` blocks


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
