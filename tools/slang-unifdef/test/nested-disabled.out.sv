// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define ENABLE_FEATURE
// CHECK-STDOUT: %b.out.sv

// The outer condition is unknown to slang-unifdef and is preserved. The nested ENABLE_FEATURE
// conditional is inside the branch that slang's normal preprocessor disables, but the
// text scanner still sees it and simplifies it.

module top;
`ifdef OUTER_DISABLED
  logic kept_in_disabled_branch;
`else
  logic outer_else;
`endif
endmodule
