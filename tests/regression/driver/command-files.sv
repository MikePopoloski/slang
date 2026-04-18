// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang -F %data/cmd.f 2>&1
// CHECK: Build succeeded

// RUN: %slang -F %data/infinite.f 2>&1 || true
// CHECK: error: command file{{.*}}includes itself recursively
