# Logic Declaration Extractor Example

This example demonstrates how to use the pyslang visitor system to extract the names of all `logic` declarations from SystemVerilog code. It provides a practical demonstration of AST traversal for code analysis and shows how to filter for specific symbol types.

## Files

- **`extract_logic_names.py`** - The main example implementation
- **`extract_logic_names_demo.py`** - A demo version with mock pyslang that can run without installation
- **`test_extract_logic_names.py`** - Tests for the example (in `../tests/`)

## What This Example Does

The example parses SystemVerilog code and identifies all variable declarations that use the `logic` data type. It demonstrates:

1. **AST Traversal**: How to visit all nodes in the syntax tree
2. **Symbol Filtering**: How to identify specific symbol types (`VariableSymbol`)
3. **Type Checking**: How to check if a variable has a specific type (`ScalarType` with `Logic` kind)
4. **Data Extraction**: How to collect information from the AST (variable names)

## Key Concepts

### Logic vs Other Types

In SystemVerilog, `logic` is one of several data types:

- **`logic`** - 4-state data type (can represent 0, 1, X, Z)
- **`bit`** - 2-state data type (can represent 0, 1)
- **`reg`** - 4-state data type (legacy, equivalent to `logic`)
- **`wire`** - Net type (not a variable)
- **`int`** - Built-in integer type

This example specifically extracts only `logic` declarations.

### AST Structure

In the slang AST:
- `logic` declarations become `VariableSymbol` nodes
- The type is represented as `ScalarType` with `scalarKind = ScalarType.Kind.Logic`
- Both port declarations and internal declarations are captured

## Usage

### Running the Real Example

```bash
python extract_logic_names.py
```

This requires a working pyslang installation.

### Running the Demo

```bash
python extract_logic_names_demo.py
```

This uses mock pyslang classes and can run without installation to demonstrate the concept.

## Example Output

Given this SystemVerilog code:

```systemverilog
module example(
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [15:0] data_out
);
    logic [3:0]  counter;
    logic        enable;
    bit          flag;        // Not logic - ignored
    reg [1:0]    state;       // Not logic - ignored
endmodule
```

The extractor will find:
- `clk`
- `data_in`
- `data_out`
- `counter`
- `enable`

But not `flag` (bit type) or `state` (reg type).

## Implementation Details

### LogicDeclarationExtractor Class

```python
class LogicDeclarationExtractor:
    def __init__(self):
        self.logic_names = []

    def __call__(self, obj):
        if isinstance(obj, pyslang.VariableSymbol):
            var_type = obj.type
            if isinstance(var_type, pyslang.ScalarType):
                if var_type.scalarKind == pyslang.ScalarType.Kind.Logic:
                    self.logic_names.append(obj.name)
```

### Key Steps

1. **Parse Code**: Use `pyslang.SyntaxTree.fromText()` to parse SystemVerilog
2. **Create Compilation**: Add the syntax tree to a compilation unit
3. **Create Visitor**: Instantiate the extractor class
4. **Visit AST**: Call `visit()` on the compilation root
5. **Extract Results**: Get the collected names from the visitor

## Extending the Example

This example can be extended to:

- Extract other data types (`bit`, `reg`, etc.)
- Include type information (vector widths, array dimensions)
- Find specific variable patterns (e.g., clock signals, reset signals)
- Generate reports or documentation
- Perform linting or code analysis

## Related Examples

This example follows the same visitor pattern as other pyslang examples:

- **Sensitivity List Extraction** (`test_timing_control_visitor` in tests)
- **Token Extraction** (`test_syntax_node_visitor` in tests)
- **Statement Counting** (`test_ast_visitor_single_counting_of_statements` in tests)

See `../tests/test_visitors.py` for more visitor pattern examples.
