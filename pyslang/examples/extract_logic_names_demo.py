# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Demo version of logic declaration extractor that shows the concept.

This is a demonstration version that shows how the logic declaration extractor
would work, but with mock pyslang functionality to allow running without
a full pyslang installation.
"""

from typing import List, Union


# Mock pyslang classes for demonstration
class MockToken:
    pass


class MockSyntaxNode:
    pass


class MockSymbol:
    def __init__(self, name: str):
        self.name = name


class MockVariableSymbol(MockSymbol):
    def __init__(self, name: str, var_type):
        super().__init__(name)
        self.type = var_type


class MockScalarType:
    class Kind:
        Bit = "Bit"
        Logic = "Logic"
        Reg = "Reg"

    def __init__(self, kind):
        self.scalarKind = kind


class MockSyntaxTree:
    @staticmethod
    def fromText(code: str):
        # This would normally parse the code
        return MockSyntaxTree()


class MockCompilation:
    def __init__(self):
        # Create some mock logic declarations based on the sample code
        self._mock_symbols = [
            MockVariableSymbol("clk", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("reset_n", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("data_in", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("data_out", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("valid_out", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("counter", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("enable", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("state", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("next_state", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("temp_data", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("ready", MockScalarType(MockScalarType.Kind.Logic)),
            MockVariableSymbol("result", MockScalarType(MockScalarType.Kind.Logic)),
            # Non-logic declarations that should be filtered out
            MockVariableSymbol("bit_signal", MockScalarType(MockScalarType.Kind.Bit)),
            MockVariableSymbol("reg_signal", MockScalarType(MockScalarType.Kind.Reg)),
            MockSymbol("wire_signal"),  # Not a VariableSymbol
            MockSymbol("int_var"),  # Not a VariableSymbol
        ]

    def addSyntaxTree(self, tree):
        pass

    def getRoot(self):
        return self

    def visit(self, visitor):
        # Simulate visiting all symbols
        for symbol in self._mock_symbols:
            visitor(symbol)


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

    def __call__(self, obj: Union[MockToken, MockSyntaxNode]) -> None:
        """Visit method called for each node in the AST.

        Args:
            obj: The current AST node being visited. Can be a Token or SyntaxNode.
                 We're specifically interested in VariableSymbol nodes.
        """
        # Check if this is a variable symbol (includes logic declarations)
        if isinstance(obj, MockVariableSymbol):
            # Get the type of the variable
            var_type = obj.type

            # Check if it's a scalar type (which includes logic, bit, reg)
            if isinstance(var_type, MockScalarType):
                # Check specifically for logic type
                if var_type.scalarKind == MockScalarType.Kind.Logic:
                    self.logic_names.append(obj.name)


def extract_logic_declaration_names(systemverilog_code: str) -> List[str]:
    """Extract logic declaration names from SystemVerilog code.

    Args:
        systemverilog_code: A string containing SystemVerilog source code.

    Returns:
        A list of strings containing the names of all logic declarations.
    """
    # Parse the SystemVerilog code into a syntax tree
    tree = MockSyntaxTree.fromText(systemverilog_code)

    # Create a compilation unit and add the syntax tree
    compilation = MockCompilation()
    compilation.addSyntaxTree(tree)

    # Create our visitor to extract logic declaration names
    extractor = LogicDeclarationExtractor()

    # Visit all nodes in the compilation root
    compilation.getRoot().visit(extractor)

    return extractor.logic_names


def main():
    """Main function demonstrating the logic declaration extractor."""

    # Sample SystemVerilog code with various logic declarations
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

    print("SystemVerilog Logic Declaration Extractor - DEMO VERSION")
    print("=" * 60)
    print()
    print("This is a demonstration version using mock pyslang functionality.")
    print("The actual implementation would work with real pyslang once installed.")
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
        print("Expected logic declarations from the sample code:")
        expected = [
            "clk",
            "reset_n",
            "data_in",
            "data_out",
            "valid_out",
            "counter",
            "enable",
            "state",
            "next_state",
            "temp_data",
            "ready",
            "result",
        ]
        print(f"  {', '.join(expected)}")

    except Exception as e:
        print(f"Error processing SystemVerilog code: {e}")


if __name__ == "__main__":
    main()
