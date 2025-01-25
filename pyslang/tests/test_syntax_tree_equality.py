# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Basic tests checking that syntax tree equality checks work as expected."""

import pyslang


def is_verilog_equal(verilog_left: str, verilog_right: str) -> bool:
    """Check if two Verilog modules are equivalent.

    Helper function for repeated check in upcoming tests.
    """
    ast_left = pyslang.SyntaxTree.fromText(verilog_left)
    ast_right = pyslang.SyntaxTree.fromText(verilog_right)
    return (ast_left.root).isEquivalentTo(ast_right.root)


def test_is_verilog_equal_when_equal() -> None:
    """Assert `is_verilog_equal` when the two Verilog modules are equal."""
    input_1 = """
        module and_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x & y;
        endmodule
    """

    input_2 = """
        module and_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x & y;
            // Comment here
        endmodule
    """

    assert is_verilog_equal(input_1, input_2) is True


def test_is_verilog_equal_when_not_equal() -> None:
    """Assert `is_verilog_equal` when the two Verilog modules are not equal."""
    input_1 = """
        module and_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x & y;
        endmodule
    """

    input_2 = """
        module or_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x | y;
        endmodule
    """

    assert is_verilog_equal(input_1, input_2) is False


def test_verilog_equality() -> None:
    """Test that two Verilog modules with minor differences are evaluated as equal."""
    input_1 = """
        module and_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x & y;
        endmodule
    """

    input_2 = """
        module and_gate (
            input wire x,
            input wire y, // Comment here
            output wire z
        );
            // Comment here
            assign z = x & y;
            /* Another comment here */
        endmodule
    """

    st1 = pyslang.SyntaxTree.fromText(input_1)
    st1_again = pyslang.SyntaxTree.fromText(input_1)
    st1_stripped = pyslang.SyntaxTree.fromText(input_1.strip())

    assert st1.root.isEquivalentTo(st1_again.root)
    assert st1.root.isEquivalentTo(st1_stripped.root)
    assert st1_again.root.isEquivalentTo(st1_stripped.root)

    st2 = pyslang.SyntaxTree.fromText(input_2)
    st2_stripped = pyslang.SyntaxTree.fromText(input_2.strip())

    assert st1_stripped.root.isEquivalentTo(st2.root)
    assert st1.root.isEquivalentTo(st2.root)
    assert st1.root.isEquivalentTo(st2_stripped.root)
