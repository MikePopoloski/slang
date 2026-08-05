# slang-unifdef

`slang-unifdef` simplifies SystemVerilog preprocessor conditionals by forcing selected
macros to be defined or undefined, then rewriting the source with inactive branches
removed.

This is useful when producing a source tree for one configuration, for example permanently
enabling a feature guarded by a macro or removing code for a disabled feature.

## Usage

```bash
slang-unifdef [options] files-or-dirs...
```

## Options

- `-D,--define <macro>` - simplify conditionals as if `<macro>` is defined
- `-U,--undefine <macro>` - simplify conditionals as if `<macro>` is undefined
- `-i,--inplace` - rewrite input files in place
- `-h,--help` - print command-line help

`--define` and `--undefine` accept comma-separated macro lists and can be repeated.
The short forms accept attached or separate names, such as `-DENABLE_CACHE` or
`-D ENABLE_CACHE`.

## Examples

Print the simplified output for one file:

```bash
slang-unifdef foo.sv -UENABLE_LOGGING
```

Rewrite a tree in place:

```bash
slang-unifdef rtl/ -DENABLE_CACHE -UENABLE_LOGGING -i
```

Force more than one macro value:

```bash
slang-unifdef rtl/ --define ENABLE_CACHE,ENABLE_PREFETCH --undefine ENABLE_LOGGING -i
```

## Behavior

For file inputs, `slang-unifdef` processes the exact paths provided. For directory inputs,
it recursively processes files ending in `.sv`, `.svh`, `.v`, or `.vh`.

Without `--inplace`, all rewritten output is written to stdout. With `--inplace`, each
input file is overwritten with its simplified contents.

The tool understands `ifdef`, `ifndef`, `elsif`, `else`, and `endif` directive structure.
When a forced macro selects a branch, the surrounding directive scaffolding is removed and
the selected branch is inlined:

```systemverilog
`ifdef ENABLE_CACHE
  logic cache_hit;
`else
  logic direct_access;
`endif
```

With `--define ENABLE_CACHE`, this becomes:

```systemverilog
  logic cache_hit;
```

If part of an `elsif` chain is still unknown, the unresolved prefix is preserved. For
example, if `MACRO_A` is unknown and `MACRO_B` is forced defined:

```systemverilog
`ifdef MACRO_A
  logic a;
`elsif MACRO_B
  logic b;
`else
  logic fallback;
`endif
```

becomes:

```systemverilog
`ifdef MACRO_A
  logic a;
`else
  logic b;
`endif
```

## Notes

The implementation works directly over source text using slang's lexer; it does not run
the full preprocessor or parse a syntax tree. Conditions are simplified only when the
conditional directive uses a simple macro name that was supplied with `--define`
or `--undefine`.
