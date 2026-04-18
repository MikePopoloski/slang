// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// --exclude-ext filters out files with the given extensions so they are never
// parsed, even when passed explicitly on the command line.
// RUN: %slang --exclude-ext=vhd,e %data/test.sv %data/test.vhd %data/test.e --show-parsed-files 2>&1
// CHECK: test.sv
// CHECK-NOT: test.vhd
// CHECK-NOT: test.e
// CHECK: Build succeeded
