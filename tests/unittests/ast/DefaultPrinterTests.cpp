// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "slang/ast/Statements.h"
#include "slang/ast/defaultAstPrinter.h"
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
    if (old_ast_json != new_ast_json){
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
    CHECK(isEqual(code));

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
}
*/

TEST_CASE("all.sv 21-26"){
std::string code = R"(
extern interface I(input a, output b);

interface I(.*);
    modport mod(input a), mod2(input a);
endinterface)";
    CHECK(isEqual(code, "sv21_26"));
}