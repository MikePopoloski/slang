// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang --foo=bar 2>&1 || true
// CHECK: unknown command line arg

// RUN: %slang --diag-column-unit=invalid 2>&1 || true
// CHECK: invalid value 'invalid'

// RUN: %slang -Ifoo/bar/baz/ --isystem=foo/bar/baz/ 2>&1 || true
// CHECK: warning: system include directory 'foo/bar/baz/':
// CHECK: no input files

// RUN: %slang -vblah.sv 2>&1 || true
// CHECK: error: 'blah.sv':

// RUN: %slang blah.sv 2>&1 || true
// CHECK: error: 'blah.sv':

// RUN: %slang --timescale=foo 2>&1 || true
// CHECK: invalid value for time scale option

// RUN: %slang --translate-off-format=a,b,c,d --translate-off-format=a,,c --translate-off-format=a,^^,c 2>&1 || true
// CHECK: invalid format for translate-off-format

// RUN: %slang --libraries-inherit-macros 2>&1 || true
// CHECK: --single-unit must be set

// RUN: %slang -F asdfasdf 2>&1 || true
// CHECK: error: command file 'asdfasdf':

// RUN: %slang -f %data/cmd2.f 2>&1 || true
// CHECK: error: unknown command line argument '--foo-bar=baz'

// RUN: %slang -F %data/cmd2.f 2>&1 || true
// CHECK: error: unknown command line argument '--foo-bar=baz'

// RUN: %slang --define-system-task '$my_task garbage_token' 2>&1 || true
// CHECK: failed to parse as a system task or function prototype

// RUN: %slang --define-system-task 'task my_task' 2>&1 || true
// CHECK: subroutine name must start with '$'

// RUN: %slang --libmap %data/twolibs.map 2>&1 || true
// CHECK: matches multiple libraries
