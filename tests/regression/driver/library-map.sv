// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The system.map maps test6.sv into library libsys; the library map also pulls
// in libmod.qv from libfoo. Both produce warnings.
// RUN: %slang %data/test6.sv --libmap %data/library/lib.map 2>&1
// CHECK: Build succeeded: 0 errors, 2 warnings

// RUN: %slang %data/test6.sv --libmap %data/library/lib.map --diag-json - 2>&1
// CHECK: "severity": "warning"
// CHECK: no top-level modules found in design
// CHECK: missing-top

// RUN: %slang --libmap %data/infinite.map 2>&1 || true
// CHECK: error: library map{{.*}}includes itself recursively
