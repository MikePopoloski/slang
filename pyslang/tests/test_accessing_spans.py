"""Test accessing `std::span` elements."""

import pyslang

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
    tree = pyslang.SyntaxTree.fromText(CASE_STATEMENT_VERILOG_1, "test.sv")

    compilation = pyslang.Compilation()
    compilation.addSyntaxTree(tree)

    # `compilation.getCompilationUnits()`, in C++, returns a `std::span` object. Check that it is
    # accessible and converted to a list with the Python bindings.
    std_span_as_list = compilation.getCompilationUnits()
    assert std_span_as_list is not None
    assert isinstance(std_span_as_list, list)
    assert len(std_span_as_list) == 1
    assert isinstance(std_span_as_list[0], pyslang.Symbol)
    assert isinstance(std_span_as_list[0], pyslang.CompilationUnitSymbol)


def test_token_construction() -> None:
    t1 = pyslang.Token()
    assert isinstance(t1, pyslang.Token)

    t2 = pyslang.Token(
        pyslang.BumpAllocator(),
        pyslang.TokenKind(12),
        [pyslang.Trivia()],  # This argument, in C++, is a `std::span` object.
        "'{",
        pyslang.SourceLocation(),
    )
    assert isinstance(t2, pyslang.Token)
