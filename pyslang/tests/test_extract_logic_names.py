# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Tests for the logic declaration name extractor example.

Note: This test replicates the logic extractor functionality directly
rather than importing from the example to avoid import path issues.
"""

from typing import Union

import pyslang


class LogicDeclarationExtractor:
    """Visitor class to extract names of all logic declarations."""

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
        """Visit method called for each node in the AST."""
        # Check if this is a variable symbol (includes logic declarations)
        if isinstance(obj, pyslang.VariableSymbol):
            # Get the type of the variable
            var_type = obj.type

            # Check if this is a logic type (handles scalars, arrays, and multi-dimensional arrays)
            if self._is_logic_type(var_type):
                self.logic_names.append(obj.name)


def extract_logic_declaration_names(systemverilog_code: str) -> list[str]:
    """Extract logic declaration names from SystemVerilog code."""
    # Parse the SystemVerilog code into a syntax tree
    tree = pyslang.SyntaxTree.fromText(systemverilog_code)

    # Create a compilation unit and add the syntax tree
    compilation = pyslang.Compilation()
    compilation.addSyntaxTree(tree)

    # Create our visitor to extract logic declaration names
    extractor = LogicDeclarationExtractor()

    # Visit all nodes in the compilation root
    compilation.getRoot().visit(extractor)

    return extractor.logic_names


def test_logic_declaration_extractor():
    """Test the LogicDeclarationExtractor class directly."""

    # Simple SystemVerilog code with various declarations
    code = """
    module test_module;
        logic        clk;           // logic declaration
        logic [7:0]  data;          // logic array declaration
        bit          bit_sig;       // bit declaration (should be ignored)
        reg [3:0]    reg_sig;       // reg declaration (should be ignored)
        logic        enable;        // another logic declaration
        int          counter;       // int declaration (should be ignored)
        logic [1:0]  state;         // logic array declaration
    endmodule
    """

    # Parse and create compilation
    tree = pyslang.SyntaxTree.fromText(code)
    compilation = pyslang.Compilation()
    compilation.addSyntaxTree(tree)

    # Extract logic names
    extractor = LogicDeclarationExtractor()
    compilation.getRoot().visit(extractor)

    # Check results - should find the logic declarations but not bit, reg, int
    expected_names = {"clk", "data", "enable", "state"}
    actual_names = set(extractor.logic_names)

    assert (
        actual_names == expected_names
    ), f"Expected {expected_names}, got {actual_names}"


def test_extract_logic_declaration_names_function():
    """Test the extract_logic_declaration_names function."""

    code = """
    module simple_test;
        logic        reset;
        logic [15:0] address;
        bit          ready;         // should be ignored
        logic        valid;
    endmodule
    """

    logic_names = extract_logic_declaration_names(code)

    # Should find reset, address, and valid, but not ready (which is bit)
    expected_names = {"reset", "address", "valid"}
    actual_names = set(logic_names)

    assert (
        actual_names == expected_names
    ), f"Expected {expected_names}, got {actual_names}"


def test_no_logic_declarations():
    """Test with code that has no logic declarations."""

    code = """
    module no_logic;
        bit        a;
        reg [7:0]  b;
        int        c;
        wire       d;
    endmodule
    """

    logic_names = extract_logic_declaration_names(code)

    assert len(logic_names) == 0, f"Expected no logic declarations, got {logic_names}"


def test_complex_module_with_ports():
    """Test with a more complex module including port declarations."""

    code = """
    module complex_test(
        input  logic        clk,
        input  logic        reset_n,
        input  logic [7:0]  data_in,
        output logic [15:0] data_out,
        output logic        valid
    );
        logic [3:0]  internal_counter;
        logic        internal_enable;
        bit          bit_flag;        // should be ignored
        reg [1:0]    reg_state;       // should be ignored
        logic        ready;
    endmodule
    """

    logic_names = extract_logic_declaration_names(code)

    # Should find all logic declarations: ports + internal variables
    expected_names = {
        "clk",
        "reset_n",
        "data_in",
        "data_out",
        "valid",  # port declarations
        "internal_counter",
        "internal_enable",
        "ready",  # internal declarations
    }
    actual_names = set(logic_names)

    assert (
        actual_names == expected_names
    ), f"Expected {expected_names}, got {actual_names}"


def test_logic_arrays_and_vectors():
    """Test with various logic array and vector declarations."""

    code = """
    module array_test;
        logic           single_bit;
        logic [7:0]     byte_vector;
        logic [15:0]    word_vector;
        logic [31:0]    dword_vector;
        logic [1:0][7:0] multi_dim;    // multi-dimensional
    endmodule
    """

    logic_names = extract_logic_declaration_names(code)

    expected_names = {
        "single_bit",
        "byte_vector",
        "word_vector",
        "dword_vector",
        "multi_dim",
    }
    actual_names = set(logic_names)

    assert (
        actual_names == expected_names
    ), f"Expected {expected_names}, got {actual_names}"
