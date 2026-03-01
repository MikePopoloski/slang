# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from typing import Union

from pyslang.ast import (
    Compilation,
    ExpressionKind,
    NamedValueExpression,
    ProceduralBlockSymbol,
    SignalEventControl,
    Statement,
    StatementKind,
    SymbolKind,
    TimedStatement,
    TimingControl,
    TimingControlKind,
    VisitAction,
)
from pyslang.parsing import Token, TokenKind
from pyslang.syntax import SyntaxKind, SyntaxNode, SyntaxTree


def test_syntax_node_visitor():
    """Test the SyntaxNode visitor by extracting the tokens of a SyntaxNode."""

    tree = SyntaxTree.fromText("always @(*)")
    tokens = []

    def handle(obj: Union[Token, SyntaxNode]) -> None:
        if isinstance(obj, Token):
            tokens.append(obj)

    assert isinstance(tree.root, SyntaxNode)
    tree.root.visit(handle)
    token_kinds = [t.kind for t in tokens]
    assert token_kinds == [
        TokenKind.AlwaysKeyword,
        TokenKind.At,
        TokenKind.OpenParenthesis,
        TokenKind.Star,
        TokenKind.CloseParenthesis,
        TokenKind.Semicolon,
    ]


def test_timing_control_visitor():
    """Test the TimingControl visitor by extracting the sensitivity list of a T-FF.

    The example module was taken from
    https://www.chipverify.com/verilog/verilog-always-block
    """

    tree = SyntaxTree.fromText("""
        module tff (input  d,
                    clk,
                    rstn,
                    output reg q);

            always @ (posedge clk or negedge rstn) begin
                if (!rstn)
                    q <= 0;
                else
                    if (d)
                        q <= ~q;
                    else
                        q <= q;
            end
        endmodule
        """)
    c = Compilation()
    c.addSyntaxTree(tree)
    insts = c.getRoot().topInstances
    assert len(insts) == 1
    always_block = list(insts[0].body)[-1]
    assert isinstance(always_block, ProceduralBlockSymbol)
    timed = always_block.body
    assert isinstance(timed, TimedStatement)
    timing_control = timed.timing
    assert isinstance(timing_control, TimingControl)

    class SensitivityListExtractor:
        def __init__(self):
            self.sensitivity_vars = []

        def __call__(self, obj: Union[Token, SyntaxNode]) -> None:
            if isinstance(obj, SignalEventControl):
                assert isinstance(obj.expr, NamedValueExpression)
                self.sensitivity_vars.append(obj.expr.getSymbolReference())

    visitor = SensitivityListExtractor()
    timing_control.visit(visitor)
    sensitivity_var_names = [v.name for v in visitor.sensitivity_vars]
    assert sensitivity_var_names == ["clk", "rstn"]


def test_ast_visitor_single_counting_of_statements():
    """Test the visitor interface in pyslang.

    Uses a port of Slang's test case:
    `tests/unittests/VisitorTests.cpp:"Test single counting of statements"`.
    """

    tree = SyntaxTree.fromText("""
module m;
    int j;
    initial begin : asdf
        j = j + 3;
        if (1) begin : baz
            static int i;
            i = i + 2;
            if (1) begin : boz
                i = i + 4;
            end
        end
    end
endmodule
    """)

    class Visitor:
        def __init__(self):
            self.statement_count = 0

        def visit(self, node: Union[Token, SyntaxNode]) -> None:
            if isinstance(node, Statement):
                self.statement_count += 1

    c = Compilation()
    c.addSyntaxTree(tree)
    v = Visitor()
    c.getRoot().visit(v.visit)
    assert v.statement_count == 11


# --- lookup_table tests ---


def test_symbol_visit_lookup_table():
    """Test that a SymbolKind lookup_table filters Symbol visits correctly."""
    tree = SyntaxTree.fromText("""
module m;
    always @(*) begin end
    always @(*) begin end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Baseline: old API with isinstance filter
    old_matches = []
    c.getRoot().visit(
        lambda n: (
            old_matches.append(n) if isinstance(n, ProceduralBlockSymbol) else None
        )
    )

    # New API: C++-side kind filter
    new_matches = []
    c.getRoot().visit(lookup_table={SymbolKind.ProceduralBlock: new_matches.append})

    assert len(new_matches) == len(old_matches)
    assert len(new_matches) == 2


def test_statement_visit_lookup_table():
    """Test that a StatementKind lookup_table filters statement visits correctly."""
    tree = SyntaxTree.fromText("""
module m;
    int j;
    initial begin
        j = j + 3;
        j = j + 5;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Baseline: old API with kind check
    old_matches = []

    def count_old(node):
        if (
            isinstance(node, Statement)
            and node.kind == StatementKind.ExpressionStatement
        ):
            old_matches.append(node)

    c.getRoot().visit(count_old)

    # New API
    new_matches = []
    c.getRoot().visit(
        lookup_table={StatementKind.ExpressionStatement: new_matches.append}
    )

    assert len(new_matches) == len(old_matches)
    assert len(new_matches) == 2


def test_expression_visit_lookup_table():
    """Test that an ExpressionKind lookup_table filters expression visits correctly.

    ASTVisitor visits expressions during Symbol.visit(), so ExpressionKind
    keys work in lookup_tables passed to root.visit().
    """
    tree = SyntaxTree.fromText("""
module m;
    int j;
    initial begin
        j = j + 3;
        j = j + 5;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Baseline: old API with kind check
    old_matches = []

    def count_old(node):
        if hasattr(node, "kind") and node.kind == ExpressionKind.NamedValue:
            old_matches.append(node)

    c.getRoot().visit(count_old)

    # New API
    new_matches = []
    c.getRoot().visit(lookup_table={ExpressionKind.NamedValue: new_matches.append})

    assert len(new_matches) == len(old_matches)
    assert len(new_matches) > 0


def test_timing_control_visit_lookup_table():
    """Test that a TimingControlKind lookup_table filters TimingControl visits correctly."""
    tree = SyntaxTree.fromText("""
        module tff (input  d,
                    clk,
                    rstn,
                    output reg q);

            always @ (posedge clk or negedge rstn) begin
                if (!rstn)
                    q <= 0;
                else
                    if (d)
                        q <= ~q;
                    else
                        q <= q;
            end
        endmodule
        """)
    c = Compilation()
    c.addSyntaxTree(tree)
    insts = c.getRoot().topInstances
    always_block = list(insts[0].body)[-1]
    timing_control = always_block.body.timing

    sensitivity_vars = []

    def handle_signal_event(node):
        assert isinstance(node.expr, NamedValueExpression)
        sensitivity_vars.append(node.expr.getSymbolReference())

    timing_control.visit(
        lookup_table={TimingControlKind.SignalEvent: handle_signal_event}
    )

    assert [v.name for v in sensitivity_vars] == ["clk", "rstn"]


def test_syntax_visit_lookup_table_syntax_kind():
    """Test that a SyntaxKind lookup_table filters SyntaxNode visits correctly."""
    tree = SyntaxTree.fromText("module m; endmodule")

    matches = []
    tree.root.visit(lookup_table={SyntaxKind.ModuleDeclaration: matches.append})

    assert len(matches) == 1


def test_syntax_visit_lookup_table_token_kind():
    """Test that a TokenKind lookup_table filters token visits (visitToken path) correctly."""
    tree = SyntaxTree.fromText("always @(*)")

    matches = []
    tree.root.visit(lookup_table={TokenKind.AlwaysKeyword: matches.append})

    assert len(matches) == 1
    assert isinstance(matches[0], Token)
    assert matches[0].kind == TokenKind.AlwaysKeyword


def test_lookup_table_visit_action_skip():
    """Test that VisitAction.Skip from a lookup_table handler suppresses child traversal."""
    tree = SyntaxTree.fromText("""
module m;
    int j;
    always @(*) begin
        j = j + 1;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Without skip: ExpressionStatement inside always block is visited
    no_skip_matches = []
    c.getRoot().visit(
        lookup_table={StatementKind.ExpressionStatement: no_skip_matches.append}
    )
    assert len(no_skip_matches) == 1

    # With skip on ProceduralBlock: children (including the ExpressionStatement) are not visited
    skip_matches = []
    c.getRoot().visit(
        lookup_table={
            SymbolKind.ProceduralBlock: lambda n: VisitAction.Skip,
            StatementKind.ExpressionStatement: skip_matches.append,
        }
    )
    assert len(skip_matches) == 0


def test_lookup_table_visit_action_interrupt():
    """Test that VisitAction.Interrupt from a lookup_table handler stops the traversal."""
    tree = SyntaxTree.fromText("""
module m;
    always @(*) begin end
    always @(*) begin end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    matches = []

    def interrupt_on_first(node):
        matches.append(node)
        return VisitAction.Interrupt

    c.getRoot().visit(lookup_table={SymbolKind.ProceduralBlock: interrupt_on_first})

    # Only the first ProceduralBlock handler fires; traversal stops immediately
    assert len(matches) == 1


def test_lookup_table_skip_on_statement():
    """Test VisitAction.Skip on a StatementKind prevents visiting nested statements.

    Skipping a Conditional statement should prevent the ExpressionStatements
    inside it from being reached, while ExpressionStatements at the same level
    are still visited.
    """
    tree = SyntaxTree.fromText("""
module m;
    int j;
    initial begin
        if (1) begin
            j = j + 1;
        end
        j = j + 2;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Without skip: both expression statements are visited
    no_skip_matches = []
    c.getRoot().visit(
        lookup_table={StatementKind.ExpressionStatement: no_skip_matches.append}
    )
    assert len(no_skip_matches) == 2

    # Skipping the Conditional prevents the nested ExpressionStatement from being visited
    skip_matches = []
    c.getRoot().visit(
        lookup_table={
            StatementKind.Conditional: lambda n: VisitAction.Skip,
            StatementKind.ExpressionStatement: skip_matches.append,
        }
    )
    assert len(skip_matches) == 1


def test_lookup_table_skip_in_syntax_visitor():
    """Test VisitAction.Skip in the SyntaxNode visitor prevents traversal into child syntax nodes."""
    tree = SyntaxTree.fromText("module m; int i; endmodule")

    # Without skip: the DataDeclaration inside the module is visited
    no_skip_matches = []
    tree.root.visit(lookup_table={SyntaxKind.DataDeclaration: no_skip_matches.append})
    assert len(no_skip_matches) == 1

    # Skipping ModuleDeclaration prevents traversal into its children
    skip_matches = []
    tree.root.visit(
        lookup_table={
            SyntaxKind.ModuleDeclaration: lambda n: VisitAction.Skip,
            SyntaxKind.DataDeclaration: skip_matches.append,
        }
    )
    assert len(skip_matches) == 0


def test_lookup_table_interrupt_on_statement():
    """Test VisitAction.Interrupt from a StatementKind handler stops the traversal."""
    tree = SyntaxTree.fromText("""
module m;
    int j;
    initial begin
        j = j + 3;
        j = j + 5;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    # Without interrupt: both expression statements are visited
    no_interrupt_matches = []
    c.getRoot().visit(
        lookup_table={StatementKind.ExpressionStatement: no_interrupt_matches.append}
    )
    assert len(no_interrupt_matches) == 2

    # Interrupt on the first ExpressionStatement: second never reached
    interrupt_matches = []

    def interrupt_on_first_stmt(node):
        interrupt_matches.append(node)
        return VisitAction.Interrupt

    c.getRoot().visit(
        lookup_table={StatementKind.ExpressionStatement: interrupt_on_first_stmt}
    )
    assert len(interrupt_matches) == 1


def test_lookup_table_interrupt_in_syntax_visitor():
    """Test VisitAction.Interrupt from a TokenKind handler stops the syntax visitor."""
    tree = SyntaxTree.fromText("always @(*)")

    # Without interrupt: all tokens are visited
    all_tokens = []
    tree.root.visit(
        lookup_table={
            TokenKind.AlwaysKeyword: all_tokens.append,
            TokenKind.At: all_tokens.append,
            TokenKind.OpenParenthesis: all_tokens.append,
            TokenKind.Star: all_tokens.append,
            TokenKind.CloseParenthesis: all_tokens.append,
            TokenKind.Semicolon: all_tokens.append,
        }
    )
    assert len(all_tokens) == 6

    # Interrupt on AlwaysKeyword: remaining tokens never visited
    interrupted_tokens = []

    def interrupt_on_always(token):
        interrupted_tokens.append(token)
        return VisitAction.Interrupt

    tree.root.visit(
        lookup_table={
            TokenKind.AlwaysKeyword: interrupt_on_always,
            TokenKind.At: interrupted_tokens.append,
            TokenKind.OpenParenthesis: interrupted_tokens.append,
            TokenKind.Star: interrupted_tokens.append,
            TokenKind.CloseParenthesis: interrupted_tokens.append,
            TokenKind.Semicolon: interrupted_tokens.append,
        }
    )
    assert len(interrupted_tokens) == 1
    assert interrupted_tokens[0].kind == TokenKind.AlwaysKeyword


def test_lookup_table_multiple_kinds_same_type():
    """Test a lookup_table with multiple SymbolKind entries, each with its own handler."""
    tree = SyntaxTree.fromText("""
module m;
    int i;
    int j;
    always @(*) begin end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    proc_matches = []
    var_matches = []
    c.getRoot().visit(
        lookup_table={
            SymbolKind.ProceduralBlock: proc_matches.append,
            SymbolKind.Variable: var_matches.append,
        }
    )

    assert len(proc_matches) == 1
    assert len(var_matches) == 2


def test_lookup_table_multiple_kinds_mixed_types():
    """Test a lookup_table mixing SymbolKind and StatementKind entries.

    Verifies that different enum types coexist correctly in the same dict,
    even if their underlying integer values might overlap.
    """
    tree = SyntaxTree.fromText("""
module m;
    int j;
    always @(*) begin
        j = j + 1;
    end
endmodule
    """)
    c = Compilation()
    c.addSyntaxTree(tree)

    proc_matches = []
    stmt_matches = []
    c.getRoot().visit(
        lookup_table={
            SymbolKind.ProceduralBlock: proc_matches.append,
            StatementKind.ExpressionStatement: stmt_matches.append,
        }
    )

    assert len(proc_matches) == 1
    assert len(stmt_matches) == 1
