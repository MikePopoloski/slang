# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pyslang


def test_cst_json_basic():
    """Test basic CST JSON serialization functionality."""
    test_code = """
    module test;
        initial $display("Hello");
    endmodule
    """

    tree = pyslang.SyntaxTree.fromText(test_code)

    # Test default serialization (full mode)
    json_str = tree.to_json()
    assert isinstance(json_str, str)
    assert "SyntaxTree" in json_str
    assert "ModuleDeclaration" in json_str


def test_cst_json_modes():
    """Test different CST JSON serialization modes."""
    test_code = "module test; endmodule"
    tree = pyslang.SyntaxTree.fromText(test_code)

    # Test full mode (default)
    json_full = tree.to_json(pyslang.CSTJsonMode.Full)
    assert "trivia" in json_full

    # Test simple trivia mode
    json_simple_trivia = tree.to_json(pyslang.CSTJsonMode.SimpleTrivia)
    assert isinstance(json_simple_trivia, str)

    # Test no trivia mode
    json_no_trivia = tree.to_json(pyslang.CSTJsonMode.NoTrivia)
    # Should not contain trivia arrays
    assert '"trivia"' not in json_no_trivia

    # Test simple tokens mode
    json_simple_tokens = tree.to_json(pyslang.CSTJsonMode.SimpleTokens)
    # Should have tokens as simple strings
    assert isinstance(json_simple_tokens, str)


def test_cst_node_serialization():
    """Test serializing individual syntax nodes."""
    test_code = "module test; endmodule"
    tree = pyslang.SyntaxTree.fromText(test_code)

    root_node = tree.root
    node_json = root_node.to_json()

    assert isinstance(node_json, str)
    assert "ModuleDeclaration" in node_json


def test_cst_node_modes():
    """Test different CST JSON modes on syntax nodes."""
    test_code = "module test; endmodule"
    tree = pyslang.SyntaxTree.fromText(test_code)
    root_node = tree.root

    # Test different modes on syntax nodes
    json_full = root_node.to_json(pyslang.CSTJsonMode.Full)
    json_simple = root_node.to_json(pyslang.CSTJsonMode.SimpleTokens)

    assert isinstance(json_full, str)
    assert isinstance(json_simple, str)
    assert "ModuleDeclaration" in json_full
    assert "ModuleDeclaration" in json_simple


def test_cst_json_mode_enum():
    """Test CSTJsonMode enum values."""
    # Test all expected enum values exist
    assert hasattr(pyslang.CSTJsonMode, "Full")
    assert hasattr(pyslang.CSTJsonMode, "SimpleTrivia")
    assert hasattr(pyslang.CSTJsonMode, "NoTrivia")
    assert hasattr(pyslang.CSTJsonMode, "SimpleTokens")

    # Test enum values are different
    modes = [
        pyslang.CSTJsonMode.Full,
        pyslang.CSTJsonMode.SimpleTrivia,
        pyslang.CSTJsonMode.NoTrivia,
        pyslang.CSTJsonMode.SimpleTokens,
    ]
    assert len(set(modes)) == 4  # All should be unique
