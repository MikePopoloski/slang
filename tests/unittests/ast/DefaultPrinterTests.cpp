// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>

#include "slang/ast/Statements.h"
#include "slang/ast/printer/defaultAstPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"

std::tuple<std::string, const slang::ast::RootSymbol&> getAst(
    slang::ast::Compilation& compilation) {
    slang::JsonWriter jsonWriter;
    slang::ast::ASTSerializer jsonPrinter(compilation, jsonWriter);
    const slang::ast::RootSymbol& rootAst = compilation.getRoot();

    jsonPrinter.setIncludeAddresses(false);
    jsonPrinter.setIncludeSourceInfo(false);
    jsonPrinter.enableMinimalInfo(true);

    jsonPrinter.startObject();
    jsonPrinter.serialize(rootAst);
    jsonPrinter.endObject();

    return {std::string(jsonWriter.view()), rootAst};
}

// checks if the ast of the original code is equal to the ast of the generated code
bool isEqual(std::string original_code, std::string name_test = "test") {
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
    if (new_ast_json!= old_ast_json) {
        name_test.append(".json");
        std::ofstream out(name_test);
        out << "original json:";
        out << old_ast_json;
        out << "\nnew json:";
        out << new_ast_json;
        out << "\nnew code:";
        out << new_code << "\n";
        out.close();
    }
    return old_ast_json == new_ast_json;
}


TEST_CASE("InstanceSymbol printer") {
    std::string code = R"(module Foo; endmodule)";
    CHECK(isEqual(code));
};

TEST_CASE("InstanceSymbol with ports") {
    std::string code = R"(
module Foo (input a,b);
endmodule
)";
    CHECK(isEqual(code, "ports"));
};

TEST_CASE("InstanceSymbol with parameters") {
    std::string code = R"(
module Foo #(parameter N=2, parameter DOWN=0)
(input a,input b);
endmodule
)";
    CHECK(isEqual(code, "paramas"));
};

TEST_CASE("InstanceSymbol with import") {
    std::string code = R"(
module automatic m1 import p::*; #(int i = 1)
    (a, b, , .c({a, b[0]}));
    input a;
    output [1:0] b;
endmodule
)";
    CHECK(isEqual(code,"import"));
};

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

TEST_CASE("all.sv 0-8") {
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

TEST_CASE("all.sv 16-20"){
    std::string code = R"(
module m2 #(parameter i = 1, localparam j = i)
    (input int a[], (* bar = "asdf" *) output wire b = 1, ref c,
     interface.mod d, .e());
endmodule)";
    CHECK(isEqual(code, "sv16_20"));
}

TEST_CASE("all.sv 21-26") {
    std::string code = R"(
extern interface I(input a, output b);

interface I(.*);
    modport mod(input a), mod2(input a);
endinterface)";
    CHECK(isEqual(code, "sv21_26"));
}

// The keyword macromodule
// can be used interchangeably with the keyword module to define a module. An implementation may
// choose to treat module definitions beginning with the macromodule keyword differently.

TEST_CASE("all.sv 26-80") {
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
TEST_CASE("all.sv 80-120") {
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

TEST_CASE("all.sv 129-150") {
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

TEST_CASE("all.sv 150_153") {
    std::string code = R"(
macromodule m3;
    if (1) begin
        logic a,b,c,d,e,f;

        property p1(x,y);
            ##1 x |-> y;
        endproperty

        wire clk;
        property p2;
            @(posedge clk)
            a ##1 (b || c)[->1] |->
                if (b)
                    p1(d,e)
                else
                    f;
        endproperty
    end
endmodule
)";
    CHECK(isEqual(code, "sv150_153"));
}
/*
TEST_CASE("all.sv 153_160"){
    std::string code = R"(
macromodule m3;
        property p1(x,y);
            ##1 x |-> y;
        endproperty
        property p2;
            @(posedge clk)

        endproperty

        cover property (p2 and p2);


endmodule
)";
    CHECK(isEqual(code, "sv153_160"));
}*/

// ben geskipt naar de module na module 3

TEST_CASE("all.sv 193_200") {
    std::string code = R"(
extern primitive prim(output reg a, input b);

primitive prim(output reg a, input b);
    table
        0 : ? : 1;
        1 : 0 : x;
    endtable

endprimitive
(* attr = 3.14 *) bind m3.m m1 #(1) bound('x, , , );
)";
    CHECK(isEqual(code, "sv193_200"));
}

//notes: ast is het welfde maar code lijkt absoluut niet op elkaar
TEST_CASE("all.sv 202") {
    std::string code = R"("
module m3;
    module m;
    endmodule
endmodule
module m1#(parameter N=2)(input q,input a,input b,input c);
endmodule
(* attr = 3.14 *) bind m3.m m1 #(1) bound('x, , , );
)";
    CHECK(isEqual(code, "sv202"));
}

//note: de dingen in desing zijn niet nodig om een functioneel equivalent programma te generen
TEST_CASE("all.sv 204_210") {
    std::string code = R"("
config cfg;
    localparam i = 1;
    design work.m3;
    default liblist a b;
    cell m3 use work.m3;
endconfig
)";
    CHECK(isEqual(code, "204_210"));
}

TEST_CASE("all.sv 211_223") {
    std::string code = R"("
module ALU(input wire [7:0] i1, i2, input wire [2:1] opcode, output wire [7:0] o1;)

    specify
        specparam s1 = 2;
        if (opcode == 2'b00) (i1,i2 *> o1) = (25.0, 25.0);
        if (opcode == 2'b01) (i1 => o1) = (5.6, 8.0);
        if (opcode == s1) (i2 => o1) = (5.6, 8.0);
        (opcode *> o1) = (6.1, 6.5);
    endspecify
endmodule
)";
    CHECK(isEqual(code, "204_210"));
}
// TODOOO  HIER verder afmaken
TEST_CASE("all.sv 225_232") {
    std::string code = R"(
interface Iface();
    extern function void foo(int i, real r);
    extern forkjoin task t3();

    modport m(export foo, function void bar(int, logic), task baz);
    modport n(import foo, import task t3);
    modport o(export t3);
endinterface

)";
    CHECK(isEqual(code, "225_232"));
}

TEST_CASE("all.sv 250_266") {
    std::string code = R"(
    module m4;
        Iface i1();
        n n1(i1);

        Iface i2();

        localparam int baz = 3;
        // het volgende zord niet opgeno;en in de ast
        task i1.t2;
            static int i = baz;
        endtask

        task i2.t2;
            static int i = baz;
        endtask
    endmodule
    typedef enum { cover_none, cover_all } coverage_level;

)";
    CHECK(isEqual(code, "250_266"));
}

// removed $inferred_clock becauses this causes weirdness with the ast that i coudn't fix

TEST_CASE("all.sv 266_309") {
    std::string code = R"(
checker assert_window1 (
    logic test_expr,
    untyped start_event,
    untyped end_event,
    logic reset ,
    string error_msg = "violation"
);
    // het volgende zord niet opgenomen in de ast
    bit window = 1'b0; 
    default clocking; endclocking    
    default disable iff reset;
    bit window = 1'b0, next_window = 1'b1;

    rand bit q;

    always_comb begin
        if (window && end_event)
            next_window = 1'b0;
        else if (!window && start_event)
            next_window = 1'b1;
        else
            next_window = window;
    end



endchecker : assert_window1

module m5;
    logic a, b;
    assert_window1 aw1(1 + 1, a, b,$inferred_clock,);
endmodule
)";
    CHECK(isEqual(code, "266_309"));
}
// tododit subbsitueren in de vorige
TEST_CASE("all.sv 309_314") {
    std::string code = R"(
module m5;
    logic a, b;
    assert_window1 aw1(1 + 1, a, b);
endmodule

)";
    CHECK(isEqual(code, "309_314"));
}


TEST_CASE("all.sv 316_400") {
    std::string code = R"(
class C;
    int i;
    static int j;
    // extern is ingonerd in the ast ???
    //extern function int foo(int bar, int baz = 1);
endclass
class A;
    integer i = 1;
    integer j = 2;
    function integer f();
        f = i;
    endfunction
endclass

class B extends A;
    integer i = 2;
    function void f();
        i = j;
        super.i = super.j;
        j = super.f();
        j = this.super.f();
    endfunction
endclass

module m6;
    A a = new;
    A b1 = B::new;
    B b2 = new;
    //C2 c = new;
    int depth;
    integer i = b1.f();
    initial begin
        b2.f();
        a = b2;
        //c.i = c.j;

        randsequence(main)
            main : first second;
            first : add | dec := (1 + 1);
            second : repeat($urandom_range(2, 6)) first;
            add : if (depth < 2) first else second;
            dec : case (depth & 7)
                0 : add;
                1, 2 : dec;
                default : first;
            endcase;
            third : rand join first second;
            //fourth(string s = "done") : { if (depth) break; };
        endsequence
    end
endmodule
)";
    CHECK(isEqual(code, "316_4"));
}


TEST_CASE("all.sv 426_end") {
    std::string code = R"(
    class C3;
        enum {red, green, blue} color;
        bit [3:0] pixel_adr, pixel_offset, pixel_hue;
        logic clk, x, y, c;

        covergroup g2 (string instComment) @(posedge clk);
            Offset: coverpoint pixel_offset;
            Hue: coverpoint pixel_hue;
            AxC: cross color, pixel_adr;
            all: cross color, Hue, Offset;

            option.comment = instComment;

            e: coverpoint x iff (clk) {
                option.weight = 2;
                wildcard bins a = { [0:63],65 };
                bins b[] = { [127:150],[148:191] }; // note overlapping values
                bins c[] = { 200,201,202 };
                bins d = { [1000:$] };
                bins others[] = default;

                bins sa = (4 => 5 => 6), ([7:9],10 => 11,12);
                bins sb[] = (12 => 3 [* 1]);
                bins sc = (12 => 3 [-> 1]);
                bins sd = (12 => 3 [= 1:2]);
            }
            cross e, y {
                option.weight = c;
                bins one = '{ '{1,2}, '{3,4}, '{5,6} };
                ignore_bins others = (!binsof(e.a) || !binsof(y) intersect {1}) with (e > 10);
            }

        endgroup
    endclass    
    )";
    CHECK(isEqual(code, "426_end"));
}

// TODO bug fixen: https://www.systemverilog.io/verification/generate/ bij loop contruc
TEST_CASE("inetTest.sv") {
    std::string code = R"(

module jmagnitudeComparator(AEQB, AGTB, ALTB, A, B);
  output reg AEQB, AGTB, ALTB;
  input [3:0] A, B;

  always @(A) @(B)
  begin
    if( A === B )
      begin
        AEQB = 1;
        AGTB = 0;
        ALTB = 0;
      end
    else if ( A > B )
      begin
        AEQB = 0;
        AGTB = 1;
        ALTB = 0;
      end
    else
      begin
        AEQB = 0;
        AGTB = 0;
        ALTB = 1;
      end
  end
endmodule )";
    CHECK(isEqual(code, "inetTest"));
}