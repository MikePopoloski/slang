// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --define-system-task '$my_task' --define-system-task 'function int $my_func(output int a)' --define-system-task 'task $my_task2(int a, string b)'

module m;
    initial begin
        int a;
        $my_task();
        $my_task(1, "hello", 3.14);
        a = $my_func(a);
        $my_task(42, "hello");
    end
endmodule
