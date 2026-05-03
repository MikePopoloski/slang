// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM requires virtual overrides to use identical argument names;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools issue only a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wvirtual-arg-name-mismatch]
// CHECK: Build succeeded

class Base;
  virtual task run(int count);
  endtask
endclass
class Derived extends Base;
  virtual task run(int n);
  endtask
endclass
