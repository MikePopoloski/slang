// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %data/test?.sv --single-unit --libraries-inherit-macros -v %data/library/libmod.qv --parse-only 2>&1 || true
// CHECK: error: unknown macro or compiler directive '`ID'
