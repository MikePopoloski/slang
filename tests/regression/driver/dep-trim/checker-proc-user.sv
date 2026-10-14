// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
module checkerProcUser(input logic clk, a);
    always @(posedge clk) begin
        myChecker c(a, posedge clk);
    end
endmodule
