// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Without a mapping, `__FILE__ names the file the way diagnostics do.
// RUN: %slang -E %s 2>&1
// CHECK: string s = "{{.*}}macro-prefix-map.sv";

// The mapped prefix is replaced, and the deeper of two matching prefixes is used.
// RUN: %slang -E %s --macro-prefix-map %data/../../regression=reg 2>&1
// CHECK: string s = "reg{{[/\\]}}driver{{[/\\]}}macro-prefix-map.sv";
// RUN: %slang -E %s --macro-prefix-map %data/../../regression=reg --macro-prefix-map %data/../../regression/driver=src 2>&1
// CHECK: string s = "src{{[/\\]}}macro-prefix-map.sv";

// A value without an '=' separator is rejected.
// RUN: %slang -E %s --macro-prefix-map %data 2>&1 || true
// CHECK: invalid format for macro-prefix-map

module m;
    string s = `__FILE__;
endmodule
