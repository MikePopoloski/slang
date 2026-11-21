// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --define-system-task 'task $my_task(int a, int b = 5)' 2>&1 || true
// CHECK: error: empty argument not allowed

module m;
    initial begin
        $my_task(, 2);
    end
endmodule
