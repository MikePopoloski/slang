// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s 2>&1 || true
// CHECK: Build failed: 1 error, 0 warnings

// The warning can be suppressed.
// RUN: %slang -Wno-format-empty-arg 2>&1 %s
// CHECK: Build succeeded: 0 errors, 0 warnings

module m;
    string s;
    initial s = $sformatf("value=%0d", );
endmodule
