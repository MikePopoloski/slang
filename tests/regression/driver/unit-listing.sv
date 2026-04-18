// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// unit_warnings.f specifies -Wno-width-trunc, which suppresses the global
// -Wwidth-trunc for files in that unit.
// RUN: %slang -Wwidth-trunc -C %data/unit_warnings.f 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

// unit_warn_enable.f specifies -Wwidth-trunc, so test5.sv produces a warning
// even without the flag set globally.
// RUN: %slang -C %data/unit_warn_enable.f 2>&1
// CHECK: width-trunc
// CHECK: Build succeeded

// unit_warn_everything.f uses -Weverything, which surfaces warnings like
// width-trunc from test5.sv even without global -W flags.
// RUN: %slang -C %data/unit_warn_everything.f 2>&1
// CHECK: width-trunc
// CHECK: Build succeeded

// unit_warn_error.f uses -Werror, which promotes the width-trunc warning to
// an error, causing the build to fail.
// RUN: %slang -Wwidth-trunc -C %data/unit_warn_error.f 2>&1 || true
// CHECK: width-trunc
// CHECK: Build failed

// unit_warn_none.f specifies -Wnone for test7.sv which has an unknown system
// task ($foo). In the default mode, unknown-sys-name is a baseline error that
// -Wnone must NOT suppress.
// RUN: %slang -C %data/unit_warn_none.f 2>&1 || true
// CHECK: unknown-sys-name
// CHECK: Build failed

// With --compat=all, unknown-sys-name is not a baseline error, so per-unit
// -Wnone successfully suppresses it.
// RUN: %slang --compat=all -C %data/unit_warn_none.f 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

// Mainline explicit -Wno-X settings should override baseline errors.
// unit_basic.f lists test7.sv with no per-unit -W flags.
// RUN: %slang -Wno-unknown-sys-name -C %data/unit_basic.f 2>&1
// CHECK: Build succeeded
