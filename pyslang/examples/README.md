# Pyslang Examples

This directory contains examples demonstrating how to use pyslang for various SystemVerilog analysis tasks.

## Examples

### `driver.py`
A basic example showing how to use the slang driver to parse and compile SystemVerilog files. This demonstrates the simplest way to use pyslang for file processing and error reporting.

### Logic Declaration Extractor
- **`extract_logic_names.py`** - Extract names of all `logic` declarations from SystemVerilog code

This example demonstrates the visitor pattern for AST traversal and shows how to:
- Filter for specific symbol types (VariableSymbol)
- Check variable data types (ScalarType with Logic kind)
- Extract and collect symbol information
- Distinguish between `logic`, `bit`, `reg`, and other data types

## Usage

Run any example:

```bash
python driver.py <systemverilog_files>
python extract_logic_names.py
```
