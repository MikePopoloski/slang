// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM requires the variables of a solve-before constraint to be integral
// or real, and forbids solve-before in nested constraint blocks, but all major
// tools accept both, so these are only diagnosed under -Wpedantic.
// RUN: %slang %s 2>&1
// CHECK-NOT: solve-before
// CHECK: Build succeeded

// RUN: %slang %s -Wpedantic 2>&1
// CHECK: -Wsolve-before-type]
// CHECK: -Wnested-solve-before]
// CHECK: Build succeeded

class DelayConfig;
  rand bit a;
  rand int min_delay;
  rand int mid_delay[$];
  constraint c_mid { solve min_delay before mid_delay; }
  constraint c_nested {
    foreach (mid_delay[i]) {
      solve a before mid_delay[i];
    }
  }
endclass
