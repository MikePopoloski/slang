// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM disallows a braced constraint_set as a top-level constraint item;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools accept it with a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wnonstandard-constraint-block]
// CHECK: Build succeeded

`define CREATE_VSEQ(SEQ_NAME, CONSTRAINTS) \
  class SEQ_NAME; \
    rand int x; \
    constraint c { CONSTRAINTS } \
  endclass : SEQ_NAME

`CREATE_VSEQ(my_vseq, {
    x inside {0, 1};
})
