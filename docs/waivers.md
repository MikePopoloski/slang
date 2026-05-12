# Diagnostic Waivers

Slang supports suppressing diagnostics through external TOML waiver files. This allows you to selectively ignore warnings and errors based on file paths, hierarchical instance paths, diagnostic names, and source content patterns.

Pass a waiver file on the command line with `--waiver-file <path>`. The flag is repeatable; rules from all files are merged additively (later files cannot override earlier rules — they're cumulative).

## File Format

Waiver files use TOML format with a top-level `waivers` array of tables. Every rule has exactly one **scope field** (`file` or `hier`) and zero or more **filter fields** (`diagnostic`, `regex`):

```toml
# File-scoped rule
[[waivers]]
file = "<glob>"
diagnostic = "<name>"      # optional: specific diagnostic(s)
regex = '<pattern>'        # optional: match source line content

# Hierarchy-scoped rule
[[waivers]]
hier = "<glob>"
diagnostic = "<name>"
regex = '<pattern>'
```

| Field        | Required | Description                                                                                                  |
|--------------|----------|--------------------------------------------------------------------------------------------------------------|
| `file`       | one of   | Glob against source file paths                                                                               |
| `hier`       | these    | Glob against hierarchical instance paths                                                                     |
| `diagnostic` | no       | Diagnostic option name or array of names (e.g., `"unused-variable"` or `["unused-variable", "width-trunc"]`) |
| `regex`      | no       | ECMAScript regex matched against source line content                                                         |

TOML *literal strings* (single-quoted, `'...'`) are recommended for `regex` to avoid having to double-escape backslashes.

## Scope: `file`

Matches diagnostics by the source file path. Without additional filters, all diagnostics in matching files are waived.

File paths are matched against the **absolute path** of each source buffer, so a glob like `"rtl/**"` will not match `/home/me/proj/rtl/foo.sv`. To match files regardless of where the project lives on disk, prefix patterns with `**/`.

```toml
# Waive everything in third-party IP
[[waivers]]
file = "**/ip/**"

# Waive unused variables in testbench code
[[waivers]]
file = "**/tb/**/*.sv"
diagnostic = "unused-variable"

# Waive a specific pattern in a specific file
[[waivers]]
file = "**/rtl/core.sv"
diagnostic = "unused-variable"
regex = '\bdebug_reg\b'
```

## Scope: `hier`

Matches diagnostics by the hierarchical instance path of the symbol. Both `.` and `/` separators are accepted and treated interchangeably.

```toml
# Waive width truncation in a specific instance
[[waivers]]
hier = "top/u_subsys/u_conv"
diagnostic = "width-trunc"

# Same rule using dot separators
[[waivers]]
hier = "top.u_subsys.u_conv"
diagnostic = "width-trunc"

# Waive in a hierarchy subtree using globs
[[waivers]]
hier = "**/u_debug*"
diagnostic = "unused-variable"

# Combine with regex to match specific line content
[[waivers]]
hier = "**/u_debug*"
diagnostic = "unused-variable"
regex = '\bdbg_status\b'
```

**Limitation: not every diagnostic carries a hierarchical path.** Hier-scope rules only match diagnostics that are tied to an AST symbol with a parent scope. Preprocessor warnings (e.g. `include-not-found`), parser-level warnings, and some structural warnings have no symbol and are silently passed through by hier rules — use `file` scope for those.

If a hier rule names a diagnostic that was issued but had no symbol, the unused-waivers summary flags it specifically (`diagnostic 'X' has no symbol; hier scope cannot match — use 'file' scope`) so you'll see it instead of the generic "no hier paths matched" message.

## Glob Patterns

Both `file` and `hier` fields support glob patterns:

| Pattern | Description                                               |
|---------|-----------------------------------------------------------|
| `*`     | Matches any characters within a single path segment       |
| `**`    | Matches any characters across path boundaries (recursive) |
| `?`     | Matches a single character                                |

Character classes (`[abc]`) are not supported.

**Examples:**
- `**/rtl/*.sv` — All `.sv` files directly in any `rtl/` directory
- `**/rtl/*.s?v` — All `.v` and `.sv` files directly in any `rtl/` directory
- `**/rtl/**/*.sv` — All `.sv` files anywhere under any `rtl/`
- `**/test_*.sv` — All files starting with `test_` in any directory
- `top/**/u_core` — Instance `u_core` anywhere under `top` (hier scope)

## Diagnostic Names

The `diagnostic` field accepts warning option names as used with the `-W` command-line flag. It can be a single name or a TOML array:

```toml
# Single diagnostic
[[waivers]]
file = "**/rtl/**"
diagnostic = "unused-variable"

# Multiple diagnostics
[[waivers]]
file = "**/rtl/**"
diagnostic = ["unused-variable", "width-trunc"]
```

Common diagnostic names:
- `unused-variable`
- `unused-implicit-net`
- `width-trunc`
- `empty-member`
- `implicit-net-port`

Use `slang --help-diagnostics` to see a list of available diagnostic names.

## Interaction with `-Werror`

Waivers are applied after severity promotion. This means a warning that has been promoted to an error via `-Werror=<name>` (or `-Werror`) will still be suppressed if a matching waiver fires. If you want a diagnostic to be both promoted and still visible, do not waive it.

## Debugging Waivers

Set the environment variable `SLANG_WAIVER_DEBUG=1` to enable verbose tracing of waiver rule evaluation. This outputs detailed information about which rules are being checked and why they match or don't match.

```bash
SLANG_WAIVER_DEBUG=1 slang --waiver-file waivers.toml rtl/*.sv
```

## Unused Waiver Detection

Slang tracks which waiver rules are applied during compilation. If any rules go unused, a one-line summary is always printed:

```
warning: 3 unused waivers (rerun with --print-unused-waivers to list)
```

Pass `--print-unused-waivers` to also print the full list, with the reason each rule was unused:

- Rules where the scope glob matched no files or hierarchy paths
- Rules where the scope matched but the diagnostic name was never seen
- Rules where the scope and diagnostic matched but the regex never matched source content
