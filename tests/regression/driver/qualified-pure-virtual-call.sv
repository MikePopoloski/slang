// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// A pure virtual method has no implementation for a call through 'super'
// to run; strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// The error can be downgraded to a warning.
// RUN: %slang %s -Wno-error=qualified-pure-virtual-call 2>&1
// CHECK: -Wqualified-pure-virtual-call]
// CHECK: Build succeeded

virtual class Base;
  pure virtual function int f();
endclass
class Derived extends Base;
  virtual function int f();
    return super.f() + 1;
  endfunction
endclass
