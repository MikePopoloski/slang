// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --define-system-task '  task $my_task(int a); ' 2>&1 || true
// CHECK: error: too many arguments for '$my_task'

module m;
    initial begin
        $my_task(1, 2);
    end
endmodule
