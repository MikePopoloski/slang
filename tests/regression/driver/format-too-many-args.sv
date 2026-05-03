// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Extra arguments to $sformat[f] beyond what the format string consumes
// produce a suppressible FormatTooManyArgs warning.
// RUN: %slang 2>&1 %s || true
// CHECK: -Wformat-too-many-args]
// CHECK: Build failed: 1 error, 0 warnings

// The warning can be suppressed.
// RUN: %slang -Wno-format-too-many-args 2>&1 %s
// CHECK: Build succeeded: 0 errors, 0 warnings

module m;
    string s;
    int x = 5;
    initial s = $sformatf("value=%0d", x, x);
endmodule
