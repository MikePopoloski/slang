# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Extract the names of all logic declarations from SystemVerilog code.

This example demonstrates how to use the pyslang visitor system to traverse
the AST and extract the names of all variables declared with the 'logic' type.
It shows a practical application of AST traversal for code analysis.

Example usage:
    python extract_logic_names.py

The script will parse a sample SystemVerilog module and print the names of
all logic declarations found in the code.
"""

from typing import Union

import pyslang


class LogicDeclarationExtractor:
    """Visitor class to extract names of all logic declarations.

    This visitor traverses the AST and collects the names of all variables
    that are declared with the 'logic' type. It demonstrates how to:
    1. Filter for specific symbol types (VariableSymbol)
    2. Check the type of variables (ScalarType with Logic kind)
    3. Extract and collect symbol names
    """

    def __init__(self):
        """Initialize the extractor with an empty list of logic variable names."""
        self.logic_names = []

    def _is_logic_type(self, var_type) -> bool:
        """Check if a type represents a logic type, including nested arrays.

        Args:
            var_type: The type to check (ScalarType or PackedArrayType)

        Returns:
            True if the type is logic or an array of logic types
        """
        # Check if it's a scalar logic type
        if isinstance(var_type, pyslang.ScalarType):
            return var_type.scalarKind == pyslang.ScalarType.Kind.Logic

        # Check if it's a packed array type
        elif isinstance(var_type, pyslang.PackedArrayType):
            # Recursively check the element type
            return self._is_logic_type(var_type.elementType)

        # Not a logic type
        return False

    def __call__(self, obj: Union[pyslang.Token, pyslang.SyntaxNode]) -> None:
        """Visit method called for each node in the AST.

        Args:
            obj: The current AST node being visited. Can be a Token or SyntaxNode.
                 We're specifically interested in VariableSymbol nodes.
        """
        # Check if this is a variable symbol (includes logic declarations)
        if isinstance(obj, pyslang.VariableSymbol):
            # Get the type of the variable
            var_type = obj.type

            # Check if this is a logic type (handles scalars, arrays, and multi-dimensional arrays)
            if self._is_logic_type(var_type):
                self.logic_names.append(obj.name)


def extract_logic_declaration_names(systemverilog_code: str) -> list[str]:
    """Extract logic declaration names from SystemVerilog code.

    Args:
        systemverilog_code: A string containing SystemVerilog source code.

    Returns:
        A list of strings containing the names of all logic declarations.

    Raises:
        Exception: If there are parsing errors or compilation issues.
    """
    try:
        # Parse the SystemVerilog code into a syntax tree
        tree = pyslang.SyntaxTree.fromText(systemverilog_code)

        # Create a compilation unit and add the syntax tree
        compilation = pyslang.Compilation()
        compilation.addSyntaxTree(tree)

        # Check for any diagnostics (errors/warnings) during compilation
        diagnostics = compilation.getAllDiagnostics()
        if diagnostics:
            error_messages = []
            for diag in diagnostics:
                if diag.isError():
                    error_messages.append(str(diag))
            if error_messages:
                raise Exception(f"Compilation errors: {'; '.join(error_messages)}")

        # Create our visitor to extract logic declaration names
        extractor = LogicDeclarationExtractor()

        # Visit all nodes in the compilation root
        compilation.getRoot().visit(extractor)

        return extractor.logic_names

    except Exception as e:
        raise Exception(f"Failed to extract logic declarations: {e}")


def extract_logic_declarations_from_file(filepath: str) -> list[str]:
    """Extract logic declaration names from a SystemVerilog file.

    Args:
        filepath: Path to a SystemVerilog file.

    Returns:
        A list of strings containing the names of all logic declarations.
    """
    try:
        with open(filepath, "r", encoding="utf-8") as file:
            content = file.read()
        return extract_logic_declaration_names(content)
    except FileNotFoundError:
        raise Exception(f"File not found: {filepath}")
    except Exception as e:
        raise Exception(f"Failed to process file {filepath}: {e}")


def main():
    """Main function demonstrating the logic declaration extractor."""

    import argparse

    parser = argparse.ArgumentParser(
        description="Extract logic declaration names from SystemVerilog code"
    )
    parser.add_argument(
        "files",
        nargs="*",
        help="SystemVerilog files to process (if none provided, uses built-in example)",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show verbose output including sample code",
    )

    args = parser.parse_args()

    print("SystemVerilog Logic Declaration Extractor")
    print("=" * 50)
    print()

    if args.files:
        # Process provided files
        for filepath in args.files:
            print(f"Processing file: {filepath}")
            try:
                logic_names = extract_logic_declarations_from_file(filepath)

                if logic_names:
                    print(f"Found {len(logic_names)} logic declarations:")
                    for i, name in enumerate(logic_names, 1):
                        print(f"  {i:2d}. {name}")
                else:
                    print("No logic declarations found.")

            except Exception as e:
                print(f"Error: {e}")
            print()
    else:
        # Use built-in example
        sample_code = """
        module example_module(
            input  logic        clk,           // Input logic signal
            input  logic        reset_n,       // Active-low reset
            input  logic [7:0]  data_in,       // 8-bit input data bus
            output logic [15:0] data_out,      // 16-bit output data bus
            output logic        valid_out      // Output valid signal
        );

            // Internal logic declarations
            logic [3:0]  counter;              // 4-bit counter
            logic        enable;               // Enable signal
            logic [1:0]  state, next_state;    // State machine signals
            logic [7:0]  temp_data;            // Temporary data storage

            // Some non-logic declarations for comparison
            bit          bit_signal;           // This is 'bit', not 'logic'
            reg [7:0]    reg_signal;           // This is 'reg', not 'logic'
            wire         wire_signal;          // This is a net, not a variable
            int          int_var;              // This is 'int', not a variable

            // More logic declarations
            logic        ready;                // Ready signal
            logic [31:0] result;               // 32-bit result

            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    counter <= 4'b0;
                    state <= 2'b00;
                end else begin
                    counter <= counter + 1;
                    state <= next_state;
                end
            end

            always_comb begin
                next_state = state + 1;
                temp_data = data_in;
                ready = (counter == 4'hF);
                data_out = {temp_data, temp_data};
                valid_out = ready;
            end

        endmodule
        """

        if args.verbose:
            print("Sample SystemVerilog code:")
            print("-" * 30)
            print(sample_code)
            print("-" * 30)
            print()

        try:
            # Extract logic declaration names
            logic_names = extract_logic_declaration_names(sample_code)

            # Display results
            if logic_names:
                print(f"Found {len(logic_names)} logic declarations:")
                print()
                for i, name in enumerate(logic_names, 1):
                    print(f"  {i:2d}. {name}")
            else:
                print("No logic declarations found.")

            print()
            print("Note: This extractor only finds variables declared with the")
            print("'logic' keyword. It excludes 'bit', 'reg', nets (wire), and")
            print("other data types, even if they are functionally similar.")
            print()
            print("Usage: python extract_logic_names.py [file1.sv file2.sv ...]")
            print("       python extract_logic_names.py --verbose  # Show sample code")

        except Exception as e:
            print(f"Error processing SystemVerilog code: {e}")
            print("Make sure pyslang is properly installed.")


if __name__ == "__main__":
    main()
