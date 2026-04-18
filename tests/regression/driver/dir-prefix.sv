// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang --dir-prefix %data/dirprefix dir_a/simple.sv 2>&1
// CHECK: Build succeeded

// Without any prefix, a relative path that does not exist under CWD fails.
// RUN: %slang dir_a/simple.sv 2>&1 || true
// CHECK: error: 'dir_a/simple.sv'

// The first prefix does not contain dir_a/simple.sv; the second does.
// RUN: %slang --dir-prefix %data/nested --dir-prefix %data/dirprefix dir_a/simple.sv 2>&1
// CHECK: Build succeeded
