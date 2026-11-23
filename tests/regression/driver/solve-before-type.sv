// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM requires the variables of a solve-before constraint to be integral
// or real; strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// The error can be downgraded; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wsolve-before-type]
// CHECK: Build succeeded

class DelayConfig;
  rand int min_delay;
  rand int mid_delay[2];
  constraint c_mid { solve min_delay before mid_delay; }
endclass
