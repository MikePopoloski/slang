// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define ENABLE_FEATURE --undefine MODE_INLINE
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef ENABLE_FEATURE logic kept; `else logic removed; `endif
`ifdef MODE_INLINE logic primary; `else logic alternate; `endif
wire`ifdef ENABLE_FEATURE signed `else unsigned `endif value;
endmodule
