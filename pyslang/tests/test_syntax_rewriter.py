import re

import pytest

import pyslang


def test_rewriter_handler_function_called_with_right_args():
    input_tree = pyslang.SyntaxTree.fromText(
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
        assert isinstance(args[0], pyslang.SyntaxNode)
        assert isinstance(args[1], pyslang.SyntaxRewriter)
        assert len(kwargs) == 0

        handler_tracker["call_count"] += 1

    assert handler_tracker["call_count"] == 0
    result = pyslang.rewrite(input_tree, handler)
    assert result is not None
    assert isinstance(result, pyslang.SyntaxTree)

    assert (
        handler_tracker["call_count"] > 0
    ), "Handler should have been called at least once"
    assert (
        handler_tracker["call_count"] >= 4
    ), "Handler should have been called at least 4 times"


def test_rewriter_with_no_changes():
    input_tree = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    result = pyslang.rewrite(input_tree, lambda _node, _rewriter: None)
    assert result is not None
    assert result.root.isEquivalentTo(expected.root) is True


def test_rewriter_remove():
    input_tree = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = pyslang.SyntaxTree.fromText(
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

    def remove_int_var(
        node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter
    ) -> None:
        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)

        check_func_called["called"] = True

        if node.kind == pyslang.SyntaxKind.DataDeclaration:
            if node[0].kind == pyslang.SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1
            else:
                return  # Go onto the next node.

            for subnode in node:
                check_func_called["SyntaxList_subnode_count"] += 1
                if subnode.kind == pyslang.SyntaxKind.IntType:
                    check_func_called["remove_match_count"] += 1
                    rewriter.remove(node)

    assert (
        check_func_called["called"] is False
    ), "Handler should not have been called yet"

    result = pyslang.rewrite(input_tree, remove_int_var)
    print(result.root)
    assert check_func_called["called"] is True, "Handler should have been called"
    assert result is not None
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
    input_tree = pyslang.SyntaxTree.fromText(input_text, "input_tree.sv")
    expected = pyslang.SyntaxTree.fromText(
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
    new_decl = pyslang.SyntaxTree.fromText("logic j;", "new.sv").root

    def insert_logic_var(node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter):
        """Insert logic j after int i."""
        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)
        check_func_called["called"] = True

        if node.kind == pyslang.SyntaxKind.DataDeclaration:
            if node[0].kind == pyslang.SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                rewriter.insert_after(node, new_decl)
                check_func_called["insertion_point_match_count"] += 1

    result = pyslang.rewrite(input_tree, insert_logic_var)
    assert result is not None
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
            pyslang.SyntaxTree.fromText(input_text, "input_tree_again.sv").root
        )
        is True
    ), "input_tree should not be modified"


def test_rewriter_insert_after_with_new_declaration_inside():
    input_tree = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
        endmodule
    """,
        "test.sv",
    )
    expected = pyslang.SyntaxTree.fromText(
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

    def insert_logic_var(node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter):
        """Insert logic j after int i."""
        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)
        check_func_called["called"] = True

        if node.kind == pyslang.SyntaxKind.DataDeclaration:
            if node[0].kind == pyslang.SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                # Create new variable declaration to insert.
                # This test is special because `new_decl` is constructed inside this handler function!
                new_decl = pyslang.SyntaxTree.fromText("logic j;", "new.sv").root

                rewriter.insert_after(node, new_decl)
                check_func_called["insertion_point_match_count"] += 1

    result = pyslang.rewrite(input_tree, insert_logic_var)
    assert result is not None
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
    input_tree = pyslang.SyntaxTree.fromText(input_text, "input_tree.sv")
    expected = pyslang.SyntaxTree.fromText(
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

    def replace_int_var(
        node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter
    ) -> None:
        """Replace int i with logic j."""
        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)
        check_func_called["called"] = True
        if node.kind == pyslang.SyntaxKind.DataDeclaration:
            if node[0].kind == pyslang.SyntaxKind.SyntaxList:
                check_func_called["SyntaxList_count"] += 1

                for subnode in node:
                    check_func_called["SyntaxList_subnode_count"] += 1
                    if subnode.kind == pyslang.SyntaxKind.IntType:
                        check_func_called["replacement_point_match_count"] += 1

                        # Create new variable declaration to insert.
                        new_decl = pyslang.SyntaxTree.fromText(
                            "logic j;", "new.sv"
                        ).root

                        rewriter.replace(node, new_decl)

    result = pyslang.rewrite(input_tree, replace_int_var)
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
            pyslang.SyntaxTree.fromText(input_text, "input_tree_again.sv").root
        )
        is True
    ), "input_tree should not be modified"


def test_rewriter_nested():
    input_tree = pyslang.SyntaxTree.fromText(
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
    expected = pyslang.SyntaxTree.fromText(
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

    def modify_struct(
        node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter
    ) -> None:
        """Modify the struct with several operations.

        Multiple operations:
            1. Remove `int int_member_to_be_removed` from the struct.
            2. Add `logic logic_member_to_insert` within the struct (at the start).
        """
        check_func_called["called"] = True

        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)

        # Handle removing `int i;` from inside struct.
        for subnode in node:
            if subnode.kind == pyslang.SyntaxKind.IntType:
                check_func_called["remove_match_count"] += 1
                rewriter.remove(node)
                break

        # Handle adding `logic j` before struct.
        if node.kind == pyslang.SyntaxKind.StructUnionMember:
            print(
                f"StructUnionMember #{check_func_called['insert_match_count']} found: {node}"
            )

            for subnode in node:
                if subnode.kind == pyslang.SyntaxKind.SeparatedList:
                    print(
                        f"SeparatedList #{check_func_called['insert_match_count']} found: {list(subnode)}"
                    )

                    token = subnode[0][0]
                    assert isinstance(token, pyslang.Token)
                    assert token.kind == pyslang.TokenKind.Identifier

                    if token.value == "logic_member_to_stay_untouched":
                        new_decl = pyslang.SyntaxTree.fromText(
                            "typedef struct{logic logic_member_to_insert;}t;", "new.sv"
                        ).root.type.members[0]

                        check_func_called["insert_match_count"] += 1

                        rewriter.insert_before(node, new_decl)

    result = pyslang.rewrite(input_tree, modify_struct)
    assert result is not None
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
    input_tree = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )
    expected = pyslang.SyntaxTree.fromText(
        """
        module m;
            int i;
            logic l;
        endmodule
    """,
        "test.sv",
    )

    def skip_module_body(
        node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter
    ) -> None:
        # Skip processing the module's body.
        if node.kind == pyslang.SyntaxKind.ModuleDeclaration:
            rewriter.remove(node)

    result = pyslang.rewrite(input_tree, skip_module_body)
    assert result is not None
    assert result.root.isEquivalentTo(expected.root) is True


def test_rewriter_handler_errors_are_propagated():
    input_str = """
        module m;
            int i;
            logic l;
        endmodule
    """
    input_tree = pyslang.SyntaxTree.fromText(input_str, "test.sv")

    def handler_with_error(
        node: pyslang.SyntaxNode, rewriter: pyslang.SyntaxRewriter
    ) -> None:
        assert isinstance(node, pyslang.SyntaxNode)
        assert isinstance(rewriter, pyslang.SyntaxRewriter)

        # Simulate an error in the handler.
        raise ValueError("This is a test error.")

    with pytest.raises(ValueError, match="This is a test error."):
        pyslang.rewrite(input_tree, handler_with_error)

    # Assert that the input_tree is unchanged.
    assert (
        input_tree.root.isEquivalentTo(
            pyslang.SyntaxTree.fromText(input_str, "test_again.sv").root
        )
        is True
    )
