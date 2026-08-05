// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define ENABLE_FEATURE --undefine MODE_INLINE
// CHECK-STDOUT: %b.out.sv

module top;
logic kept;
logic alternate;
wire signed value;
endmodule
