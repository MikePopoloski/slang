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
    json_str = pyslang.cst_to_json(tree)
    assert isinstance(json_str, str)
    assert "syntaxTrees" in json_str
    assert "CompilationUnit" in json_str
    assert "ModuleDeclaration" in json_str


def test_cst_json_modes():
    """Test different CST JSON serialization modes."""
    test_code = "module test; endmodule"
    tree = pyslang.SyntaxTree.fromText(test_code)

    # Test full mode (default)
    options_full = pyslang.CSTSerializationOptions(pyslang.CSTJsonMode.Full)
    json_full = pyslang.cst_to_json(tree, options_full)
    assert "trivia" in json_full

    # Test simple trivia mode
    options_simple_trivia = pyslang.CSTSerializationOptions(
        pyslang.CSTJsonMode.SimpleTrivia
    )
    json_simple_trivia = pyslang.cst_to_json(tree, options_simple_trivia)
    assert isinstance(json_simple_trivia, str)

    # Test no trivia mode
    options_no_trivia = pyslang.CSTSerializationOptions(pyslang.CSTJsonMode.NoTrivia)
    json_no_trivia = pyslang.cst_to_json(tree, options_no_trivia)
    # Should not contain trivia arrays
    assert '"trivia"' not in json_no_trivia

    # Test simple tokens mode
    options_simple_tokens = pyslang.CSTSerializationOptions(
        pyslang.CSTJsonMode.SimpleTokens
    )
    json_simple_tokens = pyslang.cst_to_json(tree, options_simple_tokens)
    # Should have tokens as simple strings
    assert isinstance(json_simple_tokens, str)


def test_cst_node_serialization():
    """Test serializing individual syntax nodes."""
    test_code = "module test; endmodule"
    tree = pyslang.SyntaxTree.fromText(test_code)

    root_node = tree.root()
    node_json = pyslang.cst_node_to_json(root_node)

    assert isinstance(node_json, str)
    assert "CompilationUnit" in node_json


def test_cst_serialization_options():
    """Test CSTSerializationOptions class."""
    # Test default constructor
    options = pyslang.CSTSerializationOptions()
    assert options.mode == pyslang.CSTJsonMode.Full

    # Test constructor with mode
    options = pyslang.CSTSerializationOptions(pyslang.CSTJsonMode.SimpleTokens)
    assert options.mode == pyslang.CSTJsonMode.SimpleTokens

    # Test mode assignment
    options.mode = pyslang.CSTJsonMode.NoTrivia
    assert options.mode == pyslang.CSTJsonMode.NoTrivia


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
