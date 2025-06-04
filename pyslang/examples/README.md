# Pyslang Examples

This directory contains examples demonstrating how to use pyslang for various SystemVerilog analysis tasks.

## Examples

### `driver.py`
A basic example showing how to use the slang driver to parse and compile SystemVerilog files. This demonstrates the simplest way to use pyslang for file processing and error reporting.

### Logic Declaration Extractor
- **`extract_logic_names.py`** - Extract names of all `logic` declarations from SystemVerilog code
- **`extract_logic_names_demo.py`** - Demo version that works without full pyslang installation
- **`README_logic_extractor.md`** - Detailed documentation for the logic extractor example

This example demonstrates the visitor pattern for AST traversal and shows how to:
- Filter for specific symbol types (VariableSymbol)
- Check variable data types (ScalarType with Logic kind)
- Extract and collect symbol information
- Distinguish between `logic`, `bit`, `reg`, and other data types

## Usage

Make sure pyslang is installed first:

```bash
pip install . --no-build-isolation --config-settings build-dir=build/python_build
```

Then run any example:

```bash
python driver.py <systemverilog_files>
python extract_logic_names.py
python extract_logic_names_demo.py  # Works without pyslang installation
```

## Testing

Tests for these examples can be found in `../tests/`:
- `test_visitors.py` - Tests for visitor patterns
- `test_extract_logic_names.py` - Tests for the logic declaration extractor

Run tests with:

```bash
pytest ../tests/
```
