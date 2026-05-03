// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// $sformat[f] silently tolerates a trailing empty argument (some tools
// produce them via macro expansion).
// RUN: %slang %s 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

// When a format specifier actually consumes an empty argument, a suppressible
// FormatEmptyArg warning is emitted.
// RUN: %slang -DCONSUME 2>&1 %s
// CHECK: -Wformat-empty-arg]
// CHECK: Build succeeded: 0 errors, 1 warning

// The warning can be suppressed.
// RUN: %slang -DCONSUME -Wno-format-empty-arg 2>&1 %s
// CHECK: Build succeeded: 0 errors, 0 warnings

module m;
    string s;
    int x = 5;
    initial s = $sformatf("value=%0d", x,);
`ifdef CONSUME
    string t;
    initial t = $sformatf("value=%0d", );
`endif
endmodule
