# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pyslang

testfile = """
module gray_counter (
    out    , // counter out
    clk    , //! clock
    clk1   , //! clock sample
    rst      //! **active high reset**
);

    input clk, clk1, rst;
    output [7:0] out;
    wire [7:0] out;
    reg [7:0] count;

    assign out = count;
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            count <= 8'b0;
        end else begin
            count <= count + 1;
        end
    end

endmodule
"""


def test_to_dict_conversion():
    tree = pyslang.SyntaxTree.fromText(testfile)
    assert tree.root.kind == pyslang.SyntaxKind.ModuleDeclaration

    json_output = tree.root.to_dict()
    assert isinstance(json_output, dict)


def test_to_json_conversion():
    tree = pyslang.SyntaxTree.fromText(testfile)
    assert tree.root.kind == pyslang.SyntaxKind.ModuleDeclaration

    json_output = tree.root.to_json()
    assert isinstance(json_output, str)
