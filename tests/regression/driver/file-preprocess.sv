// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang -E --comments %data/test.sv 2>&1
// CHECK: module m;
// CHECK-NEXT:     // hello
// CHECK-NEXT:     int i = 32'haa_bb??e;
// CHECK-NEXT:     string s =
// CHECK: begin end
// CHECK-NEXT: endmodule
