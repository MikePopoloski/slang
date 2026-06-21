// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Fixture for tests/regression/driver/cst-json-modes.sv. It is serialized via
// `--cst-json` in every CSTJsonMode. It intentionally contains a macro
// definition, an untaken `ifdef branch (which produces DisabledText trivia),
// line and block comments, and a stray token after `endmodule` (which becomes
// SkippedTokens trivia) so that the directive, disabled-text and skipped-token
// serialization paths all run.

`define WIDTH 8
`ifdef NOT_DEFINED
module disabled_branch;
    initial $display("never");
endmodule
`endif
// leading line comment
module m #(parameter int W = `WIDTH) (
    input  logic clk,
    output logic q
);
    /* block comment */ assign q = clk
endmodule
$
