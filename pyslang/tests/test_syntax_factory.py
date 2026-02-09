# SPDX-FileCopyrightText: Chaitanya Sharma
# SPDX-License-Identifier: MIT

import pytest
from pyslang.parsing import TokenKind, TriviaKind
from pyslang.syntax import (SyntaxFactory, SyntaxKind, SyntaxTree, clone,
                            deepClone, rewrite)

from pyslang import BumpAllocator


class TestMakeToken:
    def test_makeToken_with_explicit_text(self):
        token_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                token = rewriter.makeToken(TokenKind.Semicolon, ";", [])
                token_created["token"] = token
                assert token.kind == TokenKind.Semicolon

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "token" in token_created

    def test_makeToken_inferred_text(self):
        """Test creating a token where text is inferred from kind"""
        token_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                token = rewriter.makeToken(TokenKind.Semicolon)
                token_created["token"] = token
                assert token.kind == TokenKind.Semicolon

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "token" in token_created

    def test_makeToken_requires_explicit_text_for_identifier(self):
        """Test that makeToken raises error for tokens needing explicit text."""
        error_raised = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                try:
                    rewriter.makeToken(TokenKind.Identifier)
                except Exception as e:
                    error_raised["error"] = str(e)

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "error" in error_raised
        assert "explicit text" in error_raised["error"]

    def test_makeId(self):
        """Test creating an identifier token."""
        token_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                token = rewriter.makeId("my_identifier")
                token_created["token"] = token
                assert token.kind == TokenKind.Identifier
                assert token.value == "my_identifier"

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "token" in token_created

    def test_makeComma(self):
        token_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                token = rewriter.makeComma()
                token_created["token"] = token
                assert token.kind == TokenKind.Comma

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "token" in token_created

    def test_makeTrivia(self):
        """Test creating trivia with allocator-managed text."""
        trivia_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                trivia = rewriter.makeTrivia(TriviaKind.Whitespace, "  ")
                trivia_created["trivia"] = trivia
                assert trivia.kind == TriviaKind.Whitespace

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "trivia" in trivia_created


class TestClone:
    """Tests for clone and deepClone methods"""

    def test_shallow_clone(self):
        clone_result = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.DataDeclaration:
                cloned = rewriter.clone(node)
                clone_result["original"], clone_result["cloned"] = node, cloned
                assert cloned is not None
                assert cloned.kind == node.kind

        rewrite(
            SyntaxTree.fromText("module m; int i; endmodule", "test.sv"),
            handler,
        )
        assert "cloned" in clone_result

    def test_deepClone(self):
        """Test deep cloning a syntax node."""
        clone_result = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.DataDeclaration:
                cloned = rewriter.deepClone(node)
                clone_result["original"], clone_result["cloned"] = node, cloned
                assert cloned is not None
                assert cloned.kind == node.kind

        rewrite(
            SyntaxTree.fromText("module m; int i; endmodule", "test.sv"),
            handler,
        )
        assert "cloned" in clone_result

    def test_standalone_clone_function(self):
        tree = SyntaxTree.fromText("module m; int i; endmodule", "test.sv")

        data_decl = None
        for member in tree.root.members:
            if member.kind == SyntaxKind.DataDeclaration:
                data_decl = member
                break

        assert data_decl is not None
        cloned = clone(data_decl, BumpAllocator())
        assert cloned is not None
        assert cloned.kind == data_decl.kind

    def test_standalone_deepClone_function(self):
        """Test the standalone deepClone function."""
        tree = SyntaxTree.fromText("module m; int i; endmodule", "test.sv")

        data_decl = None
        for member in tree.root.members:
            if member.kind == SyntaxKind.DataDeclaration:
                data_decl = member
                break

        assert data_decl is not None
        cloned = deepClone(data_decl, BumpAllocator())
        assert cloned is not None
        assert cloned.kind == data_decl.kind


class TestMakeList:
    """Tests for makeList, makeSeparatedList, makeTokenList."""

    def test_makeList(self):
        """Test creating a SyntaxList from Python list."""
        list_result = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.DataDeclaration:
                # Create a list containing this node
                new_list = rewriter.makeList([node])
                list_result["list"] = new_list
                assert new_list is not None

        rewrite(
            SyntaxTree.fromText("module m; int i; endmodule", "test.sv"),
            handler,
        )
        assert "list" in list_result

    def test_makeSeparatedList(self):
        list_result = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.DataDeclaration:
                comma = rewriter.makeComma()
                cloned = rewriter.deepClone(node)
                sep_list = rewriter.makeSeparatedList([node, comma, cloned])
                list_result["sep_list"] = sep_list
                assert sep_list is not None

        rewrite(
            SyntaxTree.fromText("module m; int i; endmodule", "test.sv"),
            handler,
        )
        assert "sep_list" in list_result

    def test_makeTokenList(self):
        """Test creating a TokenList from Python list."""
        list_result = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                token_list = rewriter.makeTokenList(
                    [
                        rewriter.makeToken(TokenKind.Semicolon),
                        rewriter.makeComma(),
                    ]
                )
                list_result["token_list"] = token_list
                assert token_list is not None

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "token_list" in list_result


class TestSyntaxFactory:
    """Tests for SyntaxFactory access and methods."""

    def test_factory_property_accessible(self):
        """Test that factory property is accessible from rewriter."""
        factory_accessed = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                factory = rewriter.factory
                factory_accessed["factory"] = factory
                assert factory is not None
                assert isinstance(factory, SyntaxFactory)

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "factory" in factory_accessed

    def test_alloc_property_accessible(self):
        """Test that alloc property is accessible from rewriter."""
        alloc_accessed = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                alloc = rewriter.alloc
                alloc_accessed["alloc"] = alloc
                assert alloc is not None
                assert isinstance(alloc, BumpAllocator)

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "alloc" in alloc_accessed

    def test_factory_can_create_simple_node(self):
        node_created = {}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                factory = rewriter.factory
                # create an empty statement (just a semicolon)
                # emptyStatement signature: (label=None, attributes: SyntaxList, semicolon: Token)
                empty_stmt = factory.emptyStatement(
                    None,
                    rewriter.makeList([]),
                    rewriter.makeToken(TokenKind.Semicolon),
                )
                node_created["node"] = empty_stmt
                assert empty_stmt is not None
                assert empty_stmt.kind == SyntaxKind.EmptyStatement

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert "node" in node_created


class TestMemorySafety:
    def test_token_text_persists_within_handler(self):
        """Test that token text is copied to allocator and survives Python string GC within handler."""
        test_passed = {"passed": False}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                import gc

                tokens_created = []
                for i in range(10):
                    text = f"id_{i}"  # temp Python string
                    token = rewriter.makeId(text)
                    tokens_created.append(token)

                gc.collect()
                # tokens should still have valid text (since text is copied into allocator)
                for i, token in enumerate(tokens_created):
                    assert token.value == f"id_{i}", f"Token {i} has wrong value"

                test_passed["passed"] = True

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert test_passed["passed"], "Handler assertions should have passed"

    def test_trivia_created_successfully(self):
        """Test that trivia can be created with text allocated in the rewriter's allocator."""
        test_passed = {"passed": False}

        def handler(node, rewriter):
            if node.kind == SyntaxKind.ModuleDeclaration:
                import gc

                trivia_created = []
                for i in range(5):
                    text = " " * (i + 1)  # Temporary Python string
                    trivia = rewriter.makeTrivia(TriviaKind.Whitespace, text)
                    trivia_created.append(trivia)
                    assert trivia.kind == TriviaKind.Whitespace

                gc.collect()
                # trivia should still be valid
                assert len(trivia_created) == 5
                test_passed["passed"] = True

        rewrite(SyntaxTree.fromText("module m; endmodule", "test.sv"), handler)
        assert test_passed["passed"], "Handler assertions should have passed"


class TestRewriterIntegration:
    def test_replace_with_factory_created_node(self):
        """Test replacing a node with one created via factory."""
        replaced = {"count": 0}
        input_tree = SyntaxTree.fromText(
            """
            module m;
                int i;
            endmodule
            """,
            "test.sv",
        )

        def handler(node, rewriter):
            if node.kind == SyntaxKind.DataDeclaration:
                for subnode in node:
                    if subnode.kind == SyntaxKind.IntType:
                        factory = rewriter.factory
                        trivia = rewriter.makeTrivia(
                            TriviaKind.Whitespace, "\n                "
                        )
                        semi_with_trivia = rewriter.makeToken(
                            TokenKind.Semicolon, ";", [trivia]
                        )
                        # emptyMember signature: (attributes: SyntaxList, qualifiers: TokenList, semi: Token)
                        attributes = rewriter.makeList([])
                        qualifiers = rewriter.makeTokenList([])
                        empty_member = factory.emptyMember(
                            attributes, qualifiers, semi_with_trivia
                        )
                        rewriter.replace(node, empty_member)
                        replaced["count"] += 1
                        break

        result = rewrite(input_tree, handler)
        assert result is not None
        assert result.validate(), "Transformed tree should be valid"
        assert replaced["count"] == 1, "Should have replaced one declaration"
