// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Without --incdir-first, the local file (data/incdir_shadow.svh) is found
// before the +incdir version, which triggers a deliberate compile error.
// RUN: %slang -I %data/nested %data/incdir_first_test.sv 2>&1 || true
// CHECK: local_was_found_error

// With --incdir-first, the +incdir version is searched before the local file,
// so no error is triggered.
// RUN: %slang -I %data/nested --incdir-first %data/incdir_first_test.sv 2>&1
// CHECK: Build succeeded

// --compat=vcs should automatically enable incdir-first behavior.
// RUN: %slang -I %data/nested --compat=vcs %data/incdir_first_test.sv 2>&1
// CHECK: Build succeeded
