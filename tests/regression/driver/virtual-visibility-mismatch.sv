// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM requires virtual overrides to keep the same visibility;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// The error can be downgraded to a warning.
// RUN: %slang %s -Wno-error=virtual-visibility-mismatch 2>&1
// CHECK: -Wvirtual-visibility-mismatch]
// CHECK: Build succeeded

class Base;
  virtual protected function void f();
  endfunction
endclass
class Derived extends Base;
  virtual function void f();
  endfunction
endclass
