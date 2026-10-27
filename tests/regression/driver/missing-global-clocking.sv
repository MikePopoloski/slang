// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM requires a global clocking declaration to be visible;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error: no global clocking is available in this scope
// CHECK: Build failed: 2 errors, 0 warnings

// The error can be downgraded to a warning.
// RUN: %slang %s -Wno-error=missing-global-clocking 2>&1
// CHECK: warning: no global clocking is available in this scope [-Wmissing-global-clocking]
// CHECK: Build succeeded: 0 errors, 2 warnings

// It can also be suppressed entirely without causing any other errors.
// RUN: %slang %s -Wno-missing-global-clocking 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

module m;
  logic a, b;
  always @($global_clock) a <= $past_gclk(b);
endmodule
