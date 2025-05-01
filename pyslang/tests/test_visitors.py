# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from typing import Union

import pyslang


def test_syntax_node_visitor():
    """Test the SyntaxNode visitor by extracting the tokens of a SyntaxNode."""

    tree = pyslang.SyntaxTree.fromText("always @(*)")
    tokens = []

    def handle(obj: Union[pyslang.Token, pyslang.SyntaxNode]) -> None:
        if isinstance(obj, pyslang.Token):
            tokens.append(obj)

    assert isinstance(tree.root, pyslang.SyntaxNode)
    tree.root.visit(handle)
    token_kinds = [t.kind for t in tokens]
    assert token_kinds == [
        pyslang.TokenKind.AlwaysKeyword,
        pyslang.TokenKind.At,
        pyslang.TokenKind.OpenParenthesis,
        pyslang.TokenKind.Star,
        pyslang.TokenKind.CloseParenthesis,
        pyslang.TokenKind.Semicolon,
    ]


def test_timing_control_visitor():
    """Test the TimingControl visitor by extracting the sensitivity list of a T-FF.

    The example module was taken from
    https://www.chipverify.com/verilog/verilog-always-block
    """

    tree = pyslang.SyntaxTree.fromText(
        """
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
        """
    )
    c = pyslang.Compilation()
    c.addSyntaxTree(tree)
    insts = c.getRoot().topInstances
    assert len(insts) == 1
    always_block = list(insts[0].body)[-1]
    assert isinstance(always_block, pyslang.ProceduralBlockSymbol)
    timed = always_block.body
    assert isinstance(timed, pyslang.TimedStatement)
    timing_control = timed.timing
    assert isinstance(timing_control, pyslang.TimingControl)

    class SensitivityListExtractor:
        def __init__(self):
            self.sensitivity_vars = []

        def __call__(self, obj: Union[pyslang.Token, pyslang.SyntaxNode]) -> None:
            if isinstance(obj, pyslang.SignalEventControl):
                assert isinstance(obj.expr, pyslang.NamedValueExpression)
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

    tree = pyslang.SyntaxTree.fromText(
        """
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
    """
    )

    class Visitor:
        def __init__(self):
            self.statement_count = 0

        def visit(self, node: Union[pyslang.Token, pyslang.SyntaxNode]) -> None:
            if isinstance(node, pyslang.Statement):
                self.statement_count += 1

    c = pyslang.Compilation()
    c.addSyntaxTree(tree)
    v = Visitor()
    c.getRoot().visit(v.visit)
    assert v.statement_count == 11
