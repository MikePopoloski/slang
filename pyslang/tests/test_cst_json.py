# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import json
from functools import cache
from typing import Any, Dict, List, Union

import pyslang


def to_dict(tree, mode: pyslang.CSTJsonMode):
    json_str = tree.to_json(mode)
    return json.loads(json_str)


def get_enum_names(enum_class) -> set:
    return set([k for k in enum_class.__members__])


SYNTAX_KINDS = get_enum_names(pyslang.SyntaxKind)
TOKEN_KINDS = get_enum_names(pyslang.TokenKind)
TRIVIA_KINDS = get_enum_names(pyslang.TriviaKind)


class CSTValidator:
    """Validates CST JSON structure properties based on serialization mode."""

    def __init__(self, mode: pyslang.CSTJsonMode):
        self.mode = mode
        self.errors = list[str]()

    def validate(self, json_data: Any, path: str = "root") -> bool:
        """Validate CST JSON data and return True if valid."""
        self.errors = []
        self._validate_node(json_data, path)
        return len(self.errors) == 0

    def get_errors(self) -> List[str]:
        """Get list of validation errors."""
        return self.errors.copy()

    def _error(self, message: str, path: str):
        """Record a validation error."""
        self.errors.append(f"{path}: {message}")

    def _validate_node(self, node: Any, path: str):
        """Validate a single node in the CST."""
        if not isinstance(node, dict):
            self._error(f"Expected dict, got {type(node)}", path)
            return

        # Every node must have a 'kind' field
        if "kind" not in node:
            self._error("Missing 'kind' field", path)
            return

        kind = node["kind"]

        # Validate kind value
        if not isinstance(kind, str):
            self._error(f"'kind' must be string, got {type(kind)}", path)
            return

        # Handle special cases that are not in the enum
        special_kinds = {"SyntaxTree"}

        if kind not in (SYNTAX_KINDS | TOKEN_KINDS | special_kinds):
            self._error(f"Unknown kind '{kind}'", path)

        # Validate based on node type
        if kind in TOKEN_KINDS:
            self._validate_token(node, path)
        elif kind in SYNTAX_KINDS or kind in special_kinds:
            self._validate_syntax_node(node, path)

        # Validate trivia constraints based on mode
        self._validate_trivia_constraints(node, path)

    def _validate_token(self, token: Dict[str, Any], path: str):
        """Validate a token node."""
        kind = token["kind"]

        if self.mode == pyslang.CSTJsonMode.SimpleTokens:
            # In SimpleTokens mode, some tokens might be collapsed to strings
            return

        # Token must have 'text' field
        if "text" not in token:
            self._error(f"Token '{kind}' missing 'text' field", path)
            return

        text = token["text"]
        if not isinstance(text, str):
            self._error(f"Token 'text' must be string, got {type(text)}", path)
            return

        # Text should not be empty for most tokens
        if not text.strip() and kind not in {"Whitespace"}:
            self._error(f"Token '{kind}' has empty text", path)

        # Validate trivia if present
        if "trivia" in token:
            self._validate_trivia(token["trivia"], f"{path}.trivia")

    def _validate_syntax_node(self, node: Dict[str, Any], path: str):
        """Validate a syntax node (non-token)."""
        for key, value in node.items():
            if key == "kind":
                continue

            child_path = f"{path}.{key}"

            if isinstance(value, dict):
                self._validate_node(value, child_path)
            elif isinstance(value, list):
                for i, item in enumerate(value):
                    if isinstance(item, dict):
                        self._validate_node(item, f"{child_path}[{i}]")
                    elif self.mode == pyslang.CSTJsonMode.SimpleTokens and isinstance(
                        item, str
                    ):
                        # In SimpleTokens mode, some nested structures might be strings
                        if not item.strip():
                            self._error("Empty string value", f"{child_path}[{i}]")
                    else:
                        self._error(
                            f"Unexpected list item type {type(item)}",
                            f"{child_path}[{i}]",
                        )
            elif isinstance(value, str):
                # In SimpleTokens mode, some fields might be collapsed to strings
                if self.mode == pyslang.CSTJsonMode.SimpleTokens:
                    if not value.strip():
                        self._error("Empty string value", child_path)
                else:
                    self._error("Unexpected string value in syntax node", child_path)
            else:
                self._error(f"Unexpected value type {type(value)}", child_path)

    def _validate_trivia(self, trivia: Any, path: str):
        """Validate trivia field."""
        if self.mode == pyslang.CSTJsonMode.NoTrivia:
            self._error("Trivia should not be present in NoTrivia mode", path)
            return

        if self.mode == pyslang.CSTJsonMode.SimpleTrivia:
            if not isinstance(trivia, str):
                self._error(
                    f"Trivia should be string in SimpleTrivia mode, got {type(trivia)}",
                    path,
                )
            return

        # Full mode: trivia should be a list of trivia objects
        if self.mode == pyslang.CSTJsonMode.Full:
            if not isinstance(trivia, list):
                self._error(
                    f"Trivia should be list in Full mode, got {type(trivia)}", path
                )
                return

            for i, trivia_item in enumerate(trivia):
                if not isinstance(trivia_item, dict):
                    self._error(
                        f"Trivia item should be dict, got {type(trivia_item)}",
                        f"{path}[{i}]",
                    )
                    continue

                if "kind" not in trivia_item:
                    self._error("Trivia item missing 'kind'", f"{path}[{i}]")
                    continue

                kind = trivia_item["kind"]
                if kind not in TRIVIA_KINDS:
                    self._error(f"Unknown trivia kind '{kind}'", f"{path}[{i}]")

                if "text" not in trivia_item:
                    self._error("Trivia item missing 'text'", f"{path}[{i}]")
                    continue

                if not isinstance(trivia_item["text"], str):
                    self._error(
                        f"Trivia text should be string, got {type(trivia_item['text'])}",
                        f"{path}[{i}]",
                    )

    def _validate_trivia_constraints(self, node: Dict[str, Any], path: str):
        """Validate trivia constraints based on mode."""
        has_trivia = "trivia" in node

        if self.mode == pyslang.CSTJsonMode.NoTrivia and has_trivia:
            self._error("Node should not have trivia in NoTrivia mode", path)

        if has_trivia:
            self._validate_trivia(node["trivia"], f"{path}.trivia")


def test_cst_json():
    """Test structural properties of CST JSON across different inputs"""
    test_cases = [
        "module simple; endmodule",
        'module complex; initial $display("test"); endmodule',
        "module empty; endmodule",
        "module empty; asdf endmodule",
    ]

    for test_code in test_cases:
        tree = pyslang.SyntaxTree.fromText(test_code)

        for mode in [
            pyslang.CSTJsonMode.Full,
            pyslang.CSTJsonMode.SimpleTrivia,
            pyslang.CSTJsonMode.NoTrivia,
            pyslang.CSTJsonMode.SimpleTokens,
        ]:
            json_data = to_dict(tree, mode)

            # Verify tree has correct root structure
            assert "kind" in json_data, f"Tree JSON missing 'kind' for mode {mode}"
            assert (
                json_data["kind"] == "SyntaxTree"
            ), f"Tree kind should be 'SyntaxTree' for mode {mode}"
            assert "root" in json_data, f"Tree JSON missing 'root' for mode {mode}"

            # Run the validator
            validator = CSTValidator(mode)
            is_valid = validator.validate(json_data)
            if not is_valid:
                errors = "\n".join(validator.get_errors())
                raise AssertionError(
                    f"Validation failed for {test_code} in {mode}:\n{errors}"
                )

            # Verify that the root node matches the tree's root serialization
            assert json_data["root"] == to_dict(
                tree.root, mode
            ), f"Tree root does not match node serialization for {test_code} in {mode}"
