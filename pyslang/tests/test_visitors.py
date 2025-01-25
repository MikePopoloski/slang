# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang import *


def test_syntax_node_visitor():
    """
    Test the SyntaxNode visitor by extracting the tokens of a SyntaxNode.
    """

    tree = SyntaxTree.fromText("always @(*)")
    tokens = []

    def handle(obj):
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
    """
    Test the TimingControl visitor by extracting the sensitivit list
    of a T-FF. The example module was taken from
    https://www.chipverify.com/verilog/verilog-always-block
    """

    tree = SyntaxTree.fromText(
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

        def __call__(self, obj):
            if isinstance(obj, SignalEventControl):
                assert isinstance(obj.expr, NamedValueExpression)
                self.sensitivity_vars.append(obj.expr.getSymbolReference())

    visitor = SensitivityListExtractor()
    timing_control.visit(visitor)
    sensitivity_var_names = [v.name for v in visitor.sensitivity_vars]
    assert sensitivity_var_names == ["clk", "rstn"]


def test_ast_visitor_single_counting_of_statements():
    """
    Test the visitor interface in pyslang using a port of slang's
    tests/unittests/VisitorTests.cpp:"Test single counting of statements".
    """

    tree = SyntaxTree.fromText(
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
            self.count = 0

        def visit(self, node):
            if isinstance(node, Statement):
                self.count += 1

    c = Compilation()
    c.addSyntaxTree(tree)
    v = Visitor()
    c.getRoot().visit(v.visit)
    assert v.count == 11
