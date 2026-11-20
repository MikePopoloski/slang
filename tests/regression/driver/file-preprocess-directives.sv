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

// CHECK-STDOUT: %b.out.sv
