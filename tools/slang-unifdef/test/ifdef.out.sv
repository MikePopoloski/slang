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
  logic public_stuff;
  logic b;
`ifdef OTHER_MACRO
  logic other;
`endif
  logic public_ifdef;
endmodule
