// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --allow-use-before-declare --error-limit=2 --top=baz 2>&1 || true
// CHECK: Build failed: 1 error, 1 warning

// RUN: %slang %s --top=frob --allow-use-before-declare -DFOOBAR -Gbar=1 2>&1
// CHECK: Build succeeded

module baz;
    int k = j;
    int j = 1;

`ifndef FOOBAR
    int blah = unknown;
`endif
endmodule

module unused;
    `pragma diagnostic warn="-Wfoobaz"
endmodule

`ifdef FOOBAR
module frob #(parameter int bar);
endmodule
`endif
