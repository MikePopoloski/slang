# Rewriter

A simple tool that prints a given input file, showcasing the round-trip ability of the library.

## Description

By default, rewriter prints the input file exactly as is. This tool can be used to:
- Modify files before use in other tools
- Better understand what the preprocessor is doing
- Test the round-trip capability of the slang library

The tool accepts standard slang arguments like include directories. When a macro or include is not found, it will be skipped.

## Usage

```bash
rewriter [options] <file-name>
```

## Options

### Expansion Options
- `--expand-includes` - Expand include directives to show included content
- `--expand-macros` - Expand macro usages to show expanded content

### Filtering Options
- `--exclude-directives` - Exclude other directives in output (doesn't control include and macro directives)
- `--exclude-comments` - Exclude comments in output
- `--exclude-skipped` - Exclude skipped (error) nodes in output

### Formatting Options
- `--squash-blanklines` - Squash adjacent blank lines into one
- `--include-missing` - Include missing (auto-inserted) nodes in output
