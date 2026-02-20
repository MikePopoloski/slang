# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import re

import pytest
from pyslang.parsing import Token, TokenKind
from pyslang.syntax import SyntaxKind, SyntaxNode, SyntaxRewriter, SyntaxTree, rewrite


def test_rewriter_handler_function_called_with_right_args():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )

    handler_tracker = {"call_count": 0}

    def handler(*args, **kwargs):
        assert len(args) == 2
        assert isinstance(args[0], SyntaxNode)
        assert isinstance(args[1], SyntaxRewriter)
        assert len(kwargs) == 0

        handler_tracker["call_count"] += 1

    assert handler_tracker["call_count"] == 0
    result = rewrite(input_tree, handler)
    assert result is not None
    assert isinstance(result, SyntaxTree)

    assert result.validate()

    assert (
        handler_tracker["call_count"] > 0
    ), "Handler should have been called at least once"
    assert (
        handler_tracker["call_count"] >= 4
    ), "Handler should have been called at least 4 times"


def test_rewriter_with_no_changes():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    result = rewrite(input_tree, lambda _node, _rewriter: None)
    assert result is not None
    assert result.root.isEquivalentTo(expected.root) is True
    assert result.validate()


def test_rewriter_remove():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = SyntaxTree.fromText(
        """
        module m;
            logic l;
        endmodule
    """,
        "test.sv",
    )

    check_func_called = {
        "called": False,
        "SyntaxList_count": 0,
        "SyntaxList_subnode_count": 0,
        "remove_match_count": 0,
    }

    def remove_int_var(node: SyntaxNode, rewriter: SyntaxRewriter) -> None:
        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)

        check_func_called["called"] = True

        if node.kind == SyntaxKind.DataDeclaration:
            if node[0].kind == SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1
            else:
                return  # Go onto the next node.

            for subnode in node:
                check_func_called["SyntaxList_subnode_count"] += 1
                if subnode.kind == SyntaxKind.IntType:
                    check_func_called["remove_match_count"] += 1
                    rewriter.remove(node)

    assert (
        check_func_called["called"] is False
    ), "Handler should not have been called yet"

    result = rewrite(input_tree, remove_int_var)
    assert check_func_called["called"] is True, "Handler should have been called"
    assert result is not None
    assert result.validate()
    assert check_func_called["SyntaxList_count"] == 2
    assert check_func_called["SyntaxList_subnode_count"] == 10
    assert (
        check_func_called["remove_match_count"] == 1
    ), "Handler should have removed one match"
    assert (
        result.root.isEquivalentTo(input_tree.root) is False
    ), "input_tree should be modified"
    assert result.root.isEquivalentTo(expected.root) is True


def test_rewriter_insert_after_with_new_declaration_outside():
    input_text = """
        module m;
            int i;
        endmodule
    """
    input_tree = SyntaxTree.fromText(input_text, "input_tree.sv")
    expected = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic j;
        endmodule
    """,
        "test.sv",
    )

    check_func_called = {
        "called": False,
        "SyntaxList_count": 0,
        "SyntaxList_subnode_count": 0,
        "insertion_point_match_count": 0,
    }

    # Create new variable declaration to insert.
    new_decl = SyntaxTree.fromText("logic j;", "new.sv").root

    def insert_logic_var(node: SyntaxNode, rewriter: SyntaxRewriter):
        """Insert logic j after int i."""
        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)
        check_func_called["called"] = True

        if node.kind == SyntaxKind.DataDeclaration:
            if node[0].kind == SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                rewriter.insertAfter(node, new_decl)
                check_func_called["insertion_point_match_count"] += 1

    result = rewrite(input_tree, insert_logic_var)
    assert result is not None
    assert result.validate()
    assert check_func_called["called"] is True, "Handler should have been called"
    assert check_func_called["SyntaxList_count"] == 1
    assert (
        check_func_called["insertion_point_match_count"] == 1
    ), "Handler should have inserted one match"
    assert (
        result.root.isEquivalentTo(input_tree.root) is False
    ), "input_tree should be modified"
    assert result.root.isEquivalentTo(expected.root) is True
    assert (
        input_tree.root.isEquivalentTo(
            SyntaxTree.fromText(input_text, "input_tree_again.sv").root
        )
        is True
    ), "input_tree should not be modified"


def test_rewriter_insert_after_with_new_declaration_inside():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            int i;
        endmodule
    """,
        "test.sv",
    )
    expected = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic j;
        endmodule
    """,
        "test.sv",
    )

    check_func_called = {
        "called": False,
        "SyntaxList_count": 0,
        "SyntaxList_subnode_count": 0,
        "insertion_point_match_count": 0,
    }

    def insert_logic_var(node: SyntaxNode, rewriter: SyntaxRewriter):
        """Insert logic j after int i."""
        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)
        check_func_called["called"] = True

        if node.kind == SyntaxKind.DataDeclaration:
            if node[0].kind == SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                # Create new variable declaration to insert.
                # This test is special because `new_decl` is constructed inside this handler function!
                new_decl = SyntaxTree.fromText("logic j;", "new.sv").root

                rewriter.insertAfter(node, new_decl)
                check_func_called["insertion_point_match_count"] += 1

    result = rewrite(input_tree, insert_logic_var)
    assert result is not None
    assert result.validate()
    assert check_func_called["called"] is True, "Handler should have been called"
    assert check_func_called["SyntaxList_count"] == 1
    assert (
        check_func_called["insertion_point_match_count"] == 1
    ), "Handler should have inserted one match"
    assert (
        result.root.isEquivalentTo(input_tree.root) is False
    ), "input_tree should be modified"
    assert result.root.isEquivalentTo(expected.root) is True


def test_rewriter_replace():
    input_text = """
        module m;
            int i;
            logic l;
        endmodule
    """
    input_tree = SyntaxTree.fromText(input_text, "input_tree.sv")
    expected = SyntaxTree.fromText(
        """
        module m;
            logic j;
            logic l;
        endmodule
    """,
        "test.sv",
    )

    check_func_called = {
        "called": False,
        "SyntaxList_count": 0,
        "SyntaxList_subnode_count": 0,
        "replacement_point_match_count": 0,
    }

    def replace_int_var(node: SyntaxNode, rewriter: SyntaxRewriter) -> None:
        """Replace int i with logic j."""
        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)
        check_func_called["called"] = True
        if node.kind == SyntaxKind.DataDeclaration:
            if node[0].kind == SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                for subnode in node:
                    check_func_called["SyntaxList_subnode_count"] += 1
                    if subnode.kind == SyntaxKind.IntType:
                        check_func_called["replacement_point_match_count"] += 1

                        # Create new variable declaration to insert.
                        new_decl = SyntaxTree.fromText("logic j;", "new.sv").root

                        rewriter.replace(node, new_decl)

    result = rewrite(input_tree, replace_int_var)
    assert result.validate()
    assert check_func_called["called"] is True, "Handler should have been called"
    assert check_func_called["SyntaxList_count"] == 2
    assert check_func_called["SyntaxList_subnode_count"] == 10
    assert (
        check_func_called["replacement_point_match_count"] == 1
    ), "Handler should have replaced one match"
    assert (
        result.root.isEquivalentTo(input_tree.root) is False
    ), "input_tree should be modified"
    assert result.root.isEquivalentTo(expected.root) is True
    assert (
        input_tree.root.isEquivalentTo(
            SyntaxTree.fromText(input_text, "input_tree_again.sv").root
        )
        is True
    ), "input_tree should not be modified"


def test_rewriter_nested():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            struct {
                int int_member_to_be_removed;
                logic logic_member_to_stay_untouched;
            } s;
        endmodule
    """,
        "test.sv",
    )
    expected = SyntaxTree.fromText(
        """
        module m;
            struct {
                logic logic_member_to_insert;
                logic logic_member_to_stay_untouched;
            } s;
        endmodule
    """,
        "test.sv",
    )

    check_func_called = {
        "called": False,
        "remove_match_count": 0,
        "insert_match_count": 0,
    }

    def modify_struct(node: SyntaxNode, rewriter: SyntaxRewriter) -> None:
        """Modify the struct with several operations.

        Multiple operations:
            1. Remove `int int_member_to_be_removed` from the struct.
            2. Add `logic logic_member_to_insert` within the struct (at the start).
        """
        check_func_called["called"] = True

        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)

        # Handle removing `int i;` from inside struct.
        for subnode in node:
            if subnode.kind == SyntaxKind.IntType:
                check_func_called["remove_match_count"] += 1
                rewriter.remove(node)
                break

        # Handle adding `logic j` before struct.
        if node.kind == SyntaxKind.StructUnionMember:
            print(
                f"StructUnionMember #{check_func_called['insert_match_count']} found: {node}"
            )

            for subnode in node:
                if subnode.kind == SyntaxKind.SeparatedList:
                    print(
                        f"SeparatedList #{check_func_called['insert_match_count']} found: {list(subnode)}"
                    )

                    token = subnode[0][0]
                    assert isinstance(token, Token)
                    assert token.kind == TokenKind.Identifier

                    if token.value == "logic_member_to_stay_untouched":
                        new_decl = SyntaxTree.fromText(
                            "typedef struct{logic logic_member_to_insert;}t;", "new.sv"
                        ).root.type.members[0]

                        check_func_called["insert_match_count"] += 1

                        rewriter.insertBefore(node, new_decl)

    result = rewrite(input_tree, modify_struct)
    assert result is not None
    assert result.validate()
    assert check_func_called["called"] is True, "Handler should have been called"
    assert (
        check_func_called["remove_match_count"] == 1
    ), "Handler should have removed one match"
    assert (
        check_func_called["insert_match_count"] >= 1
    ), "Handler should have inserted one match"
    assert (
        result.root.isEquivalentTo(input_tree.root) is False
    ), "input_tree should be modified"

    def clean_whitespace(s: str) -> str:
        s = re.sub(r"\s+", " ", s).strip()
        # Remove extra spaces around operators.
        s = re.sub(r"\s*([{}();,])\s*", r"\1", s)
        return s

    result_str = clean_whitespace(str(result.root))
    expected_str = clean_whitespace(str(expected.root))
    assert result_str == expected_str
    assert result.root.isEquivalentTo(expected.root) is True


def test_rewriter_skip():
    input_tree = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )

    def skip_module_body(node: SyntaxNode, rewriter: SyntaxRewriter) -> None:
        # Skip processing the module's body.
        if node.kind == SyntaxKind.ModuleDeclaration:
            rewriter.remove(node)

    result = rewrite(input_tree, skip_module_body)
    assert result is not None
    assert result.root.isEquivalentTo(expected.root) is True
    assert result.validate()


def test_rewriter_handler_errors_are_propagated():
    input_str = """
        module m;
            int i;
            logic l;
        endmodule
    """
    input_tree = SyntaxTree.fromText(input_str, "test.sv")

    def handler_with_error(node: SyntaxNode, rewriter: SyntaxRewriter) -> None:
        assert isinstance(node, SyntaxNode)
        assert isinstance(rewriter, SyntaxRewriter)

        # Simulate an error in the handler.
        raise ValueError("This is a test error.")

    with pytest.raises(ValueError, match="This is a test error."):
        rewrite(input_tree, handler_with_error)

    # Assert that the input_tree is unchanged.
    assert (
        input_tree.root.isEquivalentTo(
            SyntaxTree.fromText(input_str, "test_again.sv").root
        )
        is True
    )
