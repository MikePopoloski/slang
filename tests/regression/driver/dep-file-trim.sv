// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// --depfile-trim with --top prunes to only the files needed for the requested top module.
// RUN: %slang %testdir/dep-trim/moduleA.sv %testdir/dep-trim/moduleB.sv %testdir/dep-trim/moduleC.sv %testdir/dep-trim/moduleD.sv --parse-only --Mmodule - --depfile-trim --top moduleB 2>&1
// CHECK: moduleA.sv
// CHECK-NEXT: moduleB.sv

// Requesting a higher-level module includes its transitive dependencies.
// RUN: %slang %testdir/dep-trim/moduleA.sv %testdir/dep-trim/moduleB.sv %testdir/dep-trim/moduleC.sv %testdir/dep-trim/moduleD.sv --parse-only --Mmodule - --depfile-trim --top moduleC 2>&1
// CHECK: moduleA.sv
// CHECK-NEXT: moduleB.sv
// CHECK-NEXT: moduleC.sv

// --depfile-sort without --depfile-trim lists all files in dependency order.
// RUN: %slang %testdir/dep-trim/moduleA.sv %testdir/dep-trim/moduleB.sv %testdir/dep-trim/moduleC.sv %testdir/dep-trim/moduleD.sv --parse-only --Mmodule - --depfile-sort 2>&1
// CHECK: moduleA.sv
// CHECK-NEXT: moduleB.sv
// CHECK-NEXT: moduleC.sv
// CHECK-NEXT: moduleD.sv

// An unknown top module name emits a warning and produces an empty depfile.
// RUN: %slang %testdir/dep-trim/moduleA.sv %testdir/dep-trim/moduleB.sv --parse-only --Mmodule - --depfile-trim --top unknownModule 2>&1
// CHECK: top module 'unknownModule' not found in any source file

// Circular dependencies are handled without infinite recursion.
// RUN: %slang %testdir/dep-trim/cycleA.sv %testdir/dep-trim/cycleB.sv --parse-only --Mmodule - --depfile-trim --top cycleA 2>&1
// CHECK: cycleB.sv
// CHECK-NEXT: cycleA.sv

// Requesting a mid-level module excludes files only needed by higher-level modules.
// RUN: %slang %testdir/dep-trim/leafA.sv %testdir/dep-trim/leafB.sv %testdir/dep-trim/mid.sv %testdir/dep-trim/top.sv --parse-only --Mmodule - --depfile-trim --top mid 2>&1
// CHECK: leafA.sv
// CHECK-NEXT: leafB.sv
// CHECK-NEXT: mid.sv

// A module referencing an unknown dependency emits a warning; the module's file is still listed.
// RUN: %slang %testdir/dep-trim/missing-src.sv --parse-only --Mmodule - --depfile-trim --top missingSrc 2>&1
// CHECK: 'missingModule' not found in any source file
// CHECK: missing-src.sv

// --depfile-trim with no --top specified warns that the result will always be empty.
// RUN: %slang %testdir/dep-trim/moduleA.sv --parse-only --Mmodule - --depfile-trim 2>&1
// CHECK: using --depfile-trim with no top modules
