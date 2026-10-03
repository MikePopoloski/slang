# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

"""Test accessing `std::span` elements."""

from pyslang.ast import (
    Compilation,
    CompilationUnitSymbol,
    ExpressionKind,
    Symbol,
    SymbolKind,
)
from pyslang.parsing import Token, TokenKind, Trivia
from pyslang.syntax import SyntaxTree

from pyslang import BumpAllocator, SourceLocation

CASE_STATEMENT_VERILOG_1 = """
module simple_alu (
    input  [1:0] opcode,  // Operation code
    input  [3:0] a,       // First operand
    input  [3:0] b,       // Second operand
    output reg [3:0] result // Result of operation
);

always @(*) begin
    case (opcode)
        2'b00: result = a + b;      // Add
        2'b01: result = a - b;      // Subtract
        2'b10: result = a & b;      // Bitwise AND
        2'b11: result = a | b;      // Bitwise OR
        default: result = 4'b0000;  // Default case
    endcase
end

endmodule
"""


def test_continuous_assign_expression_access_span() -> None:
    tree = SyntaxTree.fromText(CASE_STATEMENT_VERILOG_1, "test.sv")

    compilation = Compilation()
    compilation.addSyntaxTree(tree)

    # `compilation.getCompilationUnits()`, in C++, returns a `std::span` object. Check that it is
    # accessible and converted to a list with the Python bindings.
    std_span_as_list = compilation.getCompilationUnits()
    assert std_span_as_list is not None
    assert isinstance(std_span_as_list, list)
    assert len(std_span_as_list) == 1
    assert isinstance(std_span_as_list[0], Symbol)
    assert isinstance(std_span_as_list[0], CompilationUnitSymbol)


def test_token_construction() -> None:
    t1 = Token()
    assert isinstance(t1, Token)

    t2 = Token(
        BumpAllocator(),
        TokenKind(12),
        [Trivia()],  # This argument, in C++, is a `std::span` object.
        "'{",
        SourceLocation(),
    )
    assert isinstance(t2, Token)
    assert str(t2) == "'{"


def test_span_of_values_does_not_corrupt_ast() -> None:
    """Regression test for #1988: reading a span of by-value structs must not modify the AST."""
    tree = SyntaxTree.fromText("""
module m(output logic [7:0] o, input logic [7:0] a);
    always_comb {>>{o}} = a;
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)

    body = compilation.getRoot().topInstances[0].body
    blocks = [m for m in body if m.kind == SymbolKind.ProceduralBlock]
    lhs = blocks[0].body.expr.left

    for _ in range(2):
        streams = lhs.streams
        assert len(streams) == 1
        assert streams[0].operand.kind == ExpressionKind.NamedValue
        assert streams[0].operand.symbol.name == "o"
        assert streams[0].withExpr is None

    assert len(compilation.getAllDiagnostics()) == 0
