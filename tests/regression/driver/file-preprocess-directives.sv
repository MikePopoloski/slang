// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: echo // DEFAULT
// RUN: %slang -E %data/preprocess_directives.sv
// RUN: %slang -E %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // COMMENTS
// RUN: %slang -E --comments %data/preprocess_directives.sv
// RUN: %slang -E --comments %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // DIRECTIVES
// RUN: %slang -E --directives %data/preprocess_directives.sv
// RUN: %slang -E --directives %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // COMMENTS-AND-DIRECTIVES
// RUN: %slang -E --comments --directives %data/preprocess_directives.sv
// RUN: %slang -E --comments --directives %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv

// RUN: echo // LINES
// RUN: %slang -E --preprocess-lines %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // LINES-AND-COMMENTS
// RUN: %slang -E --preprocess-lines --comments %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines --comments %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // LINES-AND-DIRECTIVES
// RUN: %slang -E --preprocess-lines --directives %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines --directives %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // LINES-COMMENTS-AND-DIRECTIVES
// RUN: %slang -E --preprocess-lines --comments --directives %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines --comments --directives %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv

// RUN: echo // LINES-AND-SOURCE
// RUN: %slang -E --preprocess-lines --preprocess-source %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines --preprocess-source %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv
// RUN: echo // LINES-SOURCE-COMMENTS-AND-DIRECTIVES
// RUN: %slang -E --preprocess-lines --preprocess-source --comments --directives %data/preprocess_directives.sv
// RUN: %slang -E --preprocess-lines --preprocess-source --comments --directives %data/preprocess_directives.sv > %t.sv && %slang --quiet %t.sv

// CHECK-STDOUT: %b.out.sv
