// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %data/file_with_no_eol.sv %data/file_uses_define_in_file_with_no_eol.sv --single-unit 2>&1
// CHECK: Build succeeded
