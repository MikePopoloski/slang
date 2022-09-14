// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

// TODO:
// TEST_CASE("Basic test") {
//    Compilation compilation = compile(R"(
// module m;
//    localparam int i = 5;
//    int r = 3;
//    initial $display(i, r, "SDFSDF");
// endmodule
//)");
//
//    CodeGenerator codegen(compilation);
//    codegen.genInstance(*compilation.getRoot().topInstances[0]);
//    auto result = codegen.finish().toString();
//
//    CHECK("\n" + result == R"(
//; ModuleID = 'primary'
// source_filename = "primary"
//
//@0 = private global i32 3
//
// define i32 @main() {
//  br label %1
//
// 1:                                                ; preds = %0
//  ret i32 0
//}
//)");
//}
