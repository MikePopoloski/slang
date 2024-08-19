// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "slang/ast/Statements.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include <iostream>
#include <fstream>
#include <string>
#include<string_view>

std::tuple<std::string,const slang::ast::RootSymbol&>  getAst(slang::ast::Compilation& compilation){
    slang::JsonWriter jsonWriter;
    slang::ast::ASTSerializer jsonPrinter(compilation, jsonWriter);
    const slang::ast::RootSymbol& rootAst = compilation.getRoot();

    jsonPrinter.setIncludeAddresses(false);
    jsonPrinter.setIncludeSourceInfo(false);
    jsonPrinter.startObject();
    jsonPrinter.serialize(rootAst);
    jsonPrinter.endObject();

    return {std::string(jsonWriter.view()), rootAst};
}

// checks if the ast of the original code is equal to the ast of the generated code
bool isEqual(std::string original_code, std::string name_test ="test"){
    // calculate ast original code
    slang::ast::Compilation compilation;
    auto tree = slang::syntax::SyntaxTree::fromText(original_code);
    compilation.addSyntaxTree(tree);
    auto [old_ast_json, old_rootAst] = getAst(compilation);

    // regenerate the code
    slang::ast::AstPrinter printer(compilation);
    old_rootAst.visit(printer);
    std::string_view new_code = printer.str();
    std::cout << new_code;
    
    // calculate ast new code
    slang::ast::Compilation new_compilation;
    auto new_tree = slang::syntax::SyntaxTree::fromText(new_code);
    new_compilation.addSyntaxTree(new_tree);
    auto [new_ast_json, new_rootAst] = getAst(new_compilation);

    // dump the content to a file if the ast don't match
    if (true){
         name_test.append(".json");
         std::ofstream out(name_test);
         out <<"original json:";
         out << old_ast_json;
         out <<"\nnew json:";
         out << new_ast_json;
         out << "\nnew code:";
         out << new_code << "\n";
         out.close();
    }
    return old_ast_json == new_ast_json;
}
/*
TEST_CASE("lowerFirstLetter function") {
    slang::ast::AstPrinter printer;
    std::string_view test_string = "Test12345";
    CHECK(printer.lowerFirstLetter(test_string) == "test12345");

    test_string = "";
    CHECK(printer.lowerFirstLetter(test_string) == "");

    test_string = "test";
    CHECK(printer.lowerFirstLetter(test_string) == "test");
};
*/

TEST_CASE("InstanceSymbol printer") {
    std::string code = R"(module Foo; endmodule)"; 
    CHECK(isEqual(code));
};

TEST_CASE("InstanceSymbol with ports") {
    std::string code = R"(
module Foo (input a,b);
endmodule
)";
    CHECK(isEqual(code,"ports"));

};

TEST_CASE("InstanceSymbol with parameters") {
    std::string code = R"(
module Foo #(parameter N=2, parameter DOWN=0)
(input a,input b);
endmodule
)";
    CHECK(isEqual(code,"paramas"));

};
/*
TEST_CASE("InstanceSymbol with import") {
    slang::ast::AstPrinter printer;
    std::string code = R"(
module automatic m1 import p::*,f::*; #(int i = 1)
    (a, b, , .c({a, b[0]}));
    input a;
    output [1:0] b;
endmodule
)";
    CHECK(isEqual(code));
};*/


TEST_CASE("BlockStatement printer") {
    std::string code = R"(
module static BAR;
  initial begin
    fork:test_parralel
    join
    begin
    end
  end
endmodule)";
    CHECK(isEqual(code, "BlockStatement"));

};


TEST_CASE("all.sv 0-8"){
    std::string code = R"(
timeunit 1ns / 1ps;
timeprecision 1ps;
(* foo = 1 *) package static p;
timeunit 1ns;
program; endprogram
export *::*;
endpackage
)";
    CHECK(isEqual(code));
}
/*
TEST_CASE("all.sv 16-20"){
    std::string code = R"(
module m2 #(parameter i = 1, localparam j = i)
    (input int a[], (* bar = "asdf" *) output wire b = 1, ref c,
     interface.mod d, .e());
endmodule)";
    CHECK(isEqual(code, "sv16_20"));
}*/


TEST_CASE("all.sv 21-26"){
    std::string code = R"(
extern interface I(input a, output b);

interface I(.*);
    modport mod(input a), mod2(input a);
endinterface)";
    CHECK(isEqual(code, "sv21_26"));
}

/*
The keyword macromodule
can be used interchangeably with the keyword module to define a module. An implementation may choose        
to treat module definitions beginning with the macromodule keyword differently.
*/
TEST_CASE("all.sv 26-80"){
    std::string code = R"(
extern interface I(input a, output b);

interface I(.*);
    modport mod(input a), mod2(input a);
endinterface

macromodule m3;
    wire b;
    logic c;

    I d(.a(), .b());
    I d(.a(), .b());

    wor [1:0] w = 1;
    assign (supply0, weak1) #(1:2:3, 2:1:0) w = 2;

    wor u,v;
    alias {u,v} = w;

    logic f;
    event ev;
    initial begin
        repeat (3) @(negedge b) f = #2 1;
        wait (f) ++f;
        wait fork;
        wait_order (m3.ev) f++;

        fork : fkb
            static int i = 1;
            disable fork;
        join_none

        //disable m3.foo; TODO invalid statements fixe

        if (1) begin end else begin end

        unique0 casez (w)
            0, 1: ;
            default ;
        endcase

        case (w) inside
            [0: 3]: ;
        endcase
    end
    always_ff @(posedge b iff f == 1) begin
        forever break;
        repeat (f + 2) continue;
        while (1)
            ;
        for (int i = 0, j = i; i < 10; i += 2, j += i) begin end
        foreach (w[q]) begin end
    end


    always @* begin : foo
    end : foo


endmodule : m3)";
    CHECK(isEqual(code, "sv26_80"));
}
// removed     $info("Hello %s", "world")and  m2 m(, b, c, d, );
TEST_CASE("all.sv 80-120"){
    std::string code = R"(
macromodule m3;
    always_comb begin
        typedef union tagged {
            void Invalid;
            int Valid;
        } VInt;

        typedef union tagged {
            struct {
                bit [4:0] reg1, reg2, regd;
            } Add;
            union tagged {
                bit [9:0] JmpU;
                struct {
                    bit [1:0] cc;
                    bit [9:0] addr;
                } JmpC;
            } Jmp;
        } Instr;


        VInt v;
        Instr instr;
        automatic int rf[] = new [3];
        static longint pc = 'x;

  
        case (v) matches
            tagged Valid .n : $display ("v is Valid with value %d", n);
        endcase

        case (instr) matches
            tagged Add .s: case (s) matches
                            '{.*, .*, 0} : ; // no op
                            '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                          endcase
            tagged Jmp .j: case (j) matches
                            tagged JmpU .a : pc = pc + a;
                            tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                           endcase
        endcase

        if (instr matches (tagged Jmp .j) &&&
            j matches (tagged JmpC '{cc:.c,addr:.a})) begin
            pc = c[0] & a[0];
        end
        else begin
        end

    end
endmodule)";
    CHECK(isEqual(code, "sv80_128"));
}

TEST_CASE("all.sv 129-150"){
    std::string code = R"(
macromodule m3;
    always_latch begin
    end

    genvar j;
    for (genvar i = 0; i < 10; i += 2)
        if (i == 7) begin
        end

    ;

        generate
            case ($bits(w))
                0, 1: begin end
                2: begin end
                default: begin end
            endcase
        endgenerate

    assertion0: assert #0 (1 == 1) else $display("Hello!");
    assertion1: assume final (2 != 1) else $display("Hello!");

endmodule
)";
    CHECK(isEqual(code, "sv129_150"));
}

TEST_CASE("all.sv v"){
    std::string code = R"(
macromodule m3;
    if (1) begin
        logic a,b,c,d,e,f;

    end
endmodule
)";
    CHECK(isEqual(code, "sv150_180"));

}

// line 133 isin't tested because it is invalid


/*
TEST_CASE("interfaces "){
    std::string code = R"(
extern interface I1(input a, output b);
interface I1(.*);
    modport mod(input a), mod2(input a);
endinterface

macromodule m3;
    extern interface I1(input a, output b);
    interface I1(.*);
        modport mod(input a), mod2(input a), mod3(input a);
    endinterface
    I1 d(.a(), .b());
    I1 d(.c(), .d());

endmodule)";
    CHECK(isEqual(code, "interfaces"));
}
*/
// TODO bug fixen: https://www.systemverilog.io/verification/generate/ bij loop contruc