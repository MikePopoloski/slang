// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define ENABLE_FEATURE
// CHECK-STDOUT: %b.out.sv

// The `ifndef ENABLE_FEATURE branch (internal-only) is dropped and its `else
// branch is inlined without any surrounding `ifndef/`else/`endif scaffolding.

// An unrelated `ifdef block is left completely untouched, scaffolding and all.

// The opposite spelling also works: an `ifdef branch guarded by the feature
// macro is kept, and the `else branch is removed.

module top;
  logic a;
`ifndef ENABLE_FEATURE
  logic secret_internal;
  initial $display("internal only");
`else
  logic public_stuff;
`endif
  logic b;
`ifdef OTHER_MACRO
  logic other;
`endif
`ifdef ENABLE_FEATURE
  logic public_ifdef;
`else
  logic secret_ifdef;
`endif
endmodule
