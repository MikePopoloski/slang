// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --define-system-task '$my_task' --define-system-task 'function int $my_func(output int a)' --define-system-task 'task $my_task2(int a, string b)' --define-system-task 'task $my_task3(int a, int b = 5, int c = 6)'

module m;
    initial begin
        int a;
        $my_task();
        $my_task(1, "hello", 3.14);
        a = $my_func(a);
        $my_task(42, "hello");
        $my_task(a, "", , null, );
        $my_task3(1, , 3);
    end
endmodule
