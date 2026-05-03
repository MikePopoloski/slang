// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM does not permit string sub-expressions in constraint expressions;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools accept it with a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wstring-in-constraint]
// CHECK: Build succeeded

class RegField;
  rand logic [7:0] value;
  string name_str;
  function string get_name(); return name_str; endfunction
  constraint c_by_name {
    if (get_name() == "special") value inside {[1:10]};
  }
endclass
