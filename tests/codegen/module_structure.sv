// Tests that verify module-level IR structure: module ID, function names, etc.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// The IR must start with the module ID comment.
// CHECK: ModuleID = 'slang'

// Each function must appear with internal linkage.
// CHECK-DAG: define private i32 @fn_a
// CHECK-DAG: define private i32 @fn_b
// CHECK-DAG: define private i32 @fn_c

// CHECK-NOT: declare

function automatic int fn_a(int x); return x + 1; endfunction
function automatic int fn_b(int x); return x + 2; endfunction
function automatic int fn_c(int x); return x + 3; endfunction
