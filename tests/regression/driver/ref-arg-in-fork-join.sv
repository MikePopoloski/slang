// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM prohibits referencing a 'ref' argument inside fork-join_any/none;
// strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools issue only a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wref-arg-in-fork-join]
// CHECK: Build succeeded

class TimerTask;
  task run_timer(ref bit restart);
    fork
      begin
        wait(restart == 1);
      end
    join_any
  endtask
endclass
