#include "Test.h"

TEST_CASE("Simple module") {
    auto& text = "module foo(); endmodule";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::ModuleDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    CHECK(module.header->name.valueText() == "foo");
}

TEST_CASE("Simple interface") {
    auto& text = "interface foo(); endinterface";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::InterfaceDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    CHECK(module.header->name.valueText() == "foo");
}

TEST_CASE("Simple program") {
    auto& text = "program foo(); endprogram";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::ProgramDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    CHECK(module.header->name.valueText() == "foo");
}

TEST_CASE("Complex header") {
    auto& text = "(* foo = 4 *) macromodule automatic foo import blah::*, foo::bar; #(foo = bar, "
                 "parameter blah, stuff) (input wire i = 3); endmodule";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::ModuleDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    CHECK(module.header->name.valueText() == "foo");
    CHECK(module.attributes.size() == 1);
    CHECK(module.header->imports[0]->items.size() == 2);
    CHECK(module.header->parameters->declarations.size() == 3);
    CHECK(module.header->ports->kind == SyntaxKind::AnsiPortList);
}

TEST_CASE("Parameter ports") {
    auto& text = "module foo #(foo, foo [3:1][9:0] = 4:3:9, parameter blah = blah, localparam type "
                 "stuff = shortint, stuff2, stuff3 = int, Blah blahblah); endmodule";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::ModuleDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;

    auto parameters = module.header->parameters->declarations;
    REQUIRE(parameters.size() == 5);
    CHECK(parameters[0]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[1]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[2]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[2]->as<ParameterDeclarationSyntax>().declarators[0]->name.valueText() ==
          "blah");
    CHECK(parameters[3]->kind == SyntaxKind::TypeParameterDeclaration);

    auto& typeParam = parameters[3]->as<TypeParameterDeclarationSyntax>();
    REQUIRE(typeParam.declarators.size() == 3);
    CHECK(typeParam.declarators[0]->name.valueText() == "stuff");
    CHECK(typeParam.declarators[0]->assignment->type->kind == SyntaxKind::ShortIntType);
    CHECK(typeParam.declarators[1]->name.valueText() == "stuff2");
    CHECK(typeParam.declarators[2]->name.valueText() == "stuff3");

    CHECK(parameters[4]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[4]->as<ParameterDeclarationSyntax>().declarators[0]->name.valueText() ==
          "blahblah");
}

const MemberSyntax* parseModuleMember(const std::string& text, SyntaxKind kind) {
    auto fullText = "module foo; " + text + " endmodule";
    const auto& module = parseModule(fullText);

    REQUIRE(module.kind == SyntaxKind::ModuleDeclaration);
    CHECK(module.toString() == fullText);
    CHECK_DIAGNOSTICS_EMPTY;

    REQUIRE(module.members.size() == 1);
    REQUIRE(module.members[0]->kind == kind);
    return module.members[0];
}

TEST_CASE("Module members") {
    parseModuleMember("Foo #(stuff) bar(.*), baz(.clock, .rst(rst + 2));",
                      SyntaxKind::HierarchyInstantiation);
    parseModuleMember("timeunit 30ns / 40ns;", SyntaxKind::TimeUnitsDeclaration);
    parseModuleMember("timeprecision 30ns;", SyntaxKind::TimeUnitsDeclaration);
    parseModuleMember("module foo; endmodule", SyntaxKind::ModuleDeclaration);
    parseModuleMember("interface foo; endinterface", SyntaxKind::InterfaceDeclaration);
    parseModuleMember("program foo; endprogram", SyntaxKind::ProgramDeclaration);
    parseModuleMember("generate logic foo = 4; endgenerate", SyntaxKind::GenerateRegion);
    parseModuleMember("initial begin logic foo = 4; end", SyntaxKind::InitialBlock);
    parseModuleMember("final begin logic foo = 4; end", SyntaxKind::FinalBlock);
    parseModuleMember("always @* begin logic foo = 4; end", SyntaxKind::AlwaysBlock);
    parseModuleMember("always_ff @(posedge clk) begin logic foo = 4; end",
                      SyntaxKind::AlwaysFFBlock);
    parseModuleMember("input [31:0] foo, bar;", SyntaxKind::PortDeclaration);
    parseModuleMember("parameter foo = 1, bar = 2;", SyntaxKind::ParameterDeclarationStatement);
    parseModuleMember("for (genvar i = 1; i != 10; i++) parameter foo = i;",
                      SyntaxKind::LoopGenerate);
    parseModuleMember("typedef foo #(T, B) bar;", SyntaxKind::TypedefDeclaration);
    parseModuleMember("global clocking clk @foo; endclocking : clk",
                      SyntaxKind::ClockingDeclaration);
    parseModuleMember("default clocking @(posedge clk); endclocking",
                      SyntaxKind::ClockingDeclaration);
    parseModuleMember("default clocking asdf;", SyntaxKind::DefaultClockingReference);
    parseModuleMember(R"(
clocking clk @foo;
    default input #5 output #(2:1:4);
    inout foo = 3;
    input output bar, baz = 1, biz;
    output #5 boz, buz;
endclocking : clk
)",
                      SyntaxKind::ClockingDeclaration);
}

TEST_CASE("Parse buffer resize") {
    // Test the resizing codepath for the parse speculation buffer.
    parseModuleMember("parameter foo[1+1+1+1+1+1+1+1+1+1+1+1+1+1+1];",
                      SyntaxKind::ParameterDeclarationStatement);
}

const MemberSyntax* parseClassMember(const std::string& text, SyntaxKind kind) {
    auto fullText = "class foo; " + text + " endclass";
    const auto& classDecl = parseClass(fullText);

    REQUIRE(classDecl.kind == SyntaxKind::ClassDeclaration);
    CHECK(classDecl.toString() == fullText);
    CHECK_DIAGNOSTICS_EMPTY;

    REQUIRE(classDecl.items.size() == 1);
    REQUIRE(classDecl.items[0]->kind == kind);
    return classDecl.items[0];
}

TEST_CASE("Class members") {
    parseClassMember("function void blah(); endfunction", SyntaxKind::ClassMethodDeclaration);
    parseClassMember("virtual function void blah(); endfunction",
                     SyntaxKind::ClassMethodDeclaration);
    parseClassMember("static function type_id blah(); endfunction",
                     SyntaxKind::ClassMethodDeclaration);
    parseClassMember("function new; endfunction", SyntaxKind::ClassMethodDeclaration);
    parseClassMember("function new (integer i); endfunction", SyntaxKind::ClassMethodDeclaration);
}

TEST_CASE("Out of band constructor") {
    auto& text = R"(
class C;
    extern function new(int i);
endclass

function C::new(int i);
endfunction : new
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Property declarations") {
    auto& text = R"(
property p3;
    b ##1 c;
endproperty

c1: cover property (@(posedge clk) a #-# p3);
a1: assert property (@(posedge clk) a |-> p3);
)";

    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);

    auto propertyDecl = parser.parseSingleMember(SyntaxKind::ModuleDeclaration);
    auto coverStatement = parser.parseSingleMember(SyntaxKind::ModuleDeclaration);
    auto assertStatement = parser.parseSingleMember(SyntaxKind::ModuleDeclaration);

    REQUIRE(propertyDecl);
    REQUIRE(coverStatement);
    REQUIRE(assertStatement);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Trailing block names -- ok") {
    auto& text = R"(
module m1;
    property p3;
        b ##1 c;
    endproperty : p3

    if (1) foo : begin
    end : foo

    always begin : baz
    end : baz
endmodule : m1;

function foo;
endfunction : foo
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Trailing block names -- errors") {
    auto& text = R"(
module m1;
    property ;
        b ##1 c;
    endproperty : p3

    if (1) begin
    end : foo

    always begin : baz
    end : bluza
endmodule : m1;

function foo;
endfunction : foo

class C;
    function new;
    endfunction : bar
endclass : Baz
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::ExpectedIdentifier);
    CHECK(diagnostics[1].code == diag::EndNameNotEmpty);
    CHECK(diagnostics[2].code == diag::EndNameMismatch);
    CHECK(diagnostics[3].code == diag::EndNameMismatch);
    CHECK(diagnostics[4].code == diag::EndNameMismatch);
}

TEST_CASE("Struct member invalid token") {
    auto& text = R"(
module m1;
    struct { for } asdf;
endmodule : m1;
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::ImplicitNotAllowed);
    CHECK(diagnostics[1].code == diag::ExpectedDeclarator);
}

TEST_CASE("Errors for directives inside design elements") {
    auto& text = R"(
`resetall

module m1;
`resetall

    module n;
    endmodule
`default_nettype none

endmodule
`resetall
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::DirectiveInsideDesignElement);
    CHECK(diagnostics[1].code == diag::DirectiveInsideDesignElement);
}

TEST_CASE("Module instance -- missing closing paren") {
    auto& text = R"(
module m #(parameter int i) ();
endmodule

module n;
    m #(.i(3) m1();
    m #(.i(3)) m2();
    m (.i(3)) m3();
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 3);
    CHECK(diagnostics[0].code == diag::ExpectedIdentifier);
    CHECK(diagnostics[1].code == diag::ExpectedToken);
    CHECK(diagnostics[2].code == diag::ExpectedToken);
}

TEST_CASE("Decl modifier errors") {
    auto& text = R"(
module m;
    const static const const int i = 1;
    var static automatic j = 2;
    static var const k = 3;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 3);
    CHECK(diagnostics[0].code == diag::DuplicateDeclModifier);
    CHECK(diagnostics[1].code == diag::DeclModifierConflict);
    CHECK(diagnostics[2].code == diag::DeclModifierOrdering);
}

TEST_CASE("Type operator data decl without var -- error") {
    auto& text = R"(
module m;
    logic [3:0] a;
    logic [4:0] b;
    type(a + b) foo = a + b;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::TypeRefDeclVar);
}

TEST_CASE("Invalid continuous assignment") {
    auto& text = R"(
module m;
    int i;
    assign i += 4;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedContinuousAssignment);
}

TEST_CASE("Error for empty struct / union") {
    auto& text = R"(
module m;
    struct { } foo;
    union { } bar;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::ExpectedMember);
    CHECK(diagnostics[1].code == diag::ExpectedMember);
}

TEST_CASE("Error for disallowed members") {
    auto& text = R"(
interface I;
    module m; endmodule
    if (1) begin
        and (1, 2);
    end
endinterface

assign foo = 3;

module m;
    if (1) begin input i; end
    modport m(input a);
endmodule

program p;
    always begin end

    clocking f @bar;
        int i = 4;
    endclocking
endprogram

package p;
    assign foo = 3;
endpackage
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 8);
    CHECK(diagnostics[0].code == diag::NotAllowedInInterface);
    CHECK(diagnostics[1].code == diag::NotAllowedInInterface);
    CHECK(diagnostics[2].code == diag::NotAllowedInCU);
    CHECK(diagnostics[3].code == diag::NotAllowedInGenerate);
    CHECK(diagnostics[4].code == diag::NotAllowedInModule);
    CHECK(diagnostics[5].code == diag::NotAllowedInProgram);
    CHECK(diagnostics[6].code == diag::NotAllowedInClocking);
    CHECK(diagnostics[7].code == diag::NotAllowedInPackage);
}

TEST_CASE("Task / constructor parse errors") {
    auto& text = R"(
task int t;
endtask

function int this.bar;
endfunction

class C;
    task new();
    endtask

    function int new();
    endfunction

    function new::bar();
    endfunction
endclass

function new();
endfunction

function C::D::baz();
endfunction
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 7);
    CHECK(diagnostics[0].code == diag::TaskReturnType);
    CHECK(diagnostics[1].code == diag::ExpectedSubroutineName);
    CHECK(diagnostics[2].code == diag::TaskConstructor);
    CHECK(diagnostics[3].code == diag::ConstructorReturnType);
    CHECK(diagnostics[4].code == diag::NewKeywordQualified);
    CHECK(diagnostics[5].code == diag::ConstructorOutsideClass);
    CHECK(diagnostics[6].code == diag::ExpectedSubroutineName);
}

TEST_CASE("super.new parsing") {
    auto& text = R"(
class A;
    function new;
        super.new();
    endfunction

    int i = super.new();
endclass

class B extends A;
    function new;
        int i = 4;
        this.super.new();
        super.new();
    endfunction
endclass
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::InvalidSuperNew);
    CHECK(diagnostics[1].code == diag::InvalidSuperNew);
}

TEST_CASE("Bind directive parsing") {
    auto& text = R"(
module m1 #(parameter int i)(input logic f);
endmodule;

bind targetScope.foo[3].bar m1 #(3) a(1);
bind other: b1, $root.b1[1] m1 #(4) b(0);
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Missing semicolon error recovery") {
    auto& text = R"(
module test;
    int a
    int b;
endmodule
)";

    parseCompilationUnit(text);

    std::string result = "\n" + reportGlobalDiags();
    CHECK(result == R"(
source:3:10: error: expected ';'
    int a
         ^
)");
}

TEST_CASE("Net decl errors") {
    auto& text = R"(
module m;
    wire reg p;
    wire (supply0, supply1) q;
    wire (small) r;
    wire (strong1, pull1) s = 1;
    wire (highz0, highz1) t = 1;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::RegAfterNettype);
    CHECK(diagnostics[1].code == diag::InitializerRequired);
    CHECK(diagnostics[2].code == diag::ChargeWithTriReg);
    CHECK(diagnostics[3].code == diag::DriveStrengthInvalid);
    CHECK(diagnostics[4].code == diag::DriveStrengthHighZ);
}

TEST_CASE("Gate strength errors") {
    auto& text = R"(
module m;
    pullup (supply0, highz1) a(foo);
    pullup (highz1) b(foo);
    pullup (strong0) c(foo);
    pullup (strong1) d(foo);
    cmos (supply0, highz1) e(foo);
    tran #1 f(foo);
    and #(1,2,3) g(foo, 1, 1);
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 6);
    CHECK(diagnostics[0].code == diag::PullStrengthHighZ);
    CHECK(diagnostics[1].code == diag::PullStrengthHighZ);
    CHECK(diagnostics[2].code == diag::InvalidPullStrength);
    CHECK(diagnostics[3].code == diag::DriveStrengthNotAllowed);
    CHECK(diagnostics[4].code == diag::DelaysNotAllowed);
    CHECK(diagnostics[5].code == diag::Delay3NotAllowed);
}

TEST_CASE("Subroutine prototype errors") {
    auto& text = R"(
import "DPI-C" function automatic void foo();
import "DPI-C" function void foo::bar();
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::LifetimeForPrototype);
    CHECK(diagnostics[1].code == diag::SubroutinePrototypeScoped);
}

TEST_CASE("UDP parsing") {
    auto& text = R"(
primitive multiplexer (mux, control, dataA, dataB);
  output mux;
  input control, dataA, dataB;
  table
    0 1 0 : 1 ;
    0 1 1 : 1 ;
    0 1 x : 1 ;
  endtable
endprimitive

primitive d_edge_ff (q, clock, data);
  output q; reg q;
  input clock, data;
  table
    (01) 0 : ? : 0 ;
    (0?) 1 : 1 : 1 ;
    (?0) ? : ? : - ;
    ? (??) : ? : - ;
  endtable
endprimitive
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("specify block") {
    auto& text = R"(
module m;
    specify
        specparam f = 1, g = 2;
        showcancelled out;
        pulsestyle_ondetect out;
        if (opcode == 2'b10) (i2 => o1) = (5.6, 8.0);
        ( negedge clk => ( q[0] +: data ) ) = (20, 12);
        ifnone (i2 => o1) = 15.0, 15.0;
        (s *> q) = 1;
        (a, b, c *> q1, q2) = 10;
        (In1 +=> q) = In_to_q;
        (In1 -=> q) = In_to_q;
        (In1 +*> q) = In_to_q;
        (In1 -*> q) = In_to_q;
        $setuphold( posedge clk, data, tSU, tHLD );
        $recrem( posedge clear, posedge clk, tREC, tREM );
        $timeskew (posedge CP &&& MODE, negedge CPN, 50, , event_based_flag, remain_active_flag);
        $setup( data, posedge clk &&& (clr===0), 10 );
        $width(edge[01, 0x, x1] clr);
    endspecify
endmodule
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Invalid package decls") {
    auto& text = R"(
package p1 import p::*;;
endpackage

package p2 #(parameter int foo);
endpackage

package p3 ();
endpackage
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 3);
    CHECK(diagnostics[0].code == diag::InvalidPackageDecl);
    CHECK(diagnostics[1].code == diag::InvalidPackageDecl);
    CHECK(diagnostics[2].code == diag::InvalidPackageDecl);
}

TEST_CASE("Invalid imports in def header") {
    auto& text = R"(
module m import p::*;;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedPortList);
}

TEST_CASE("Misplaced wire keyword in data type") {
    auto& text = R"(
function wire [3:0] asdf;
endfunction
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::WireDataType);
}

TEST_CASE("Checker declaration parsing") {
    auto& text = R"(
module m;
  checker check(input in1, input sequence s_f);
    default clocking cb_checker;
    always @(s_f)
      $display("sequence triggered");

    a4: assert property (a |=> in1);

    function bit next_window (bit win);
        if (reset || win && end_flag)
            return 1'b0;
    endfunction

    rand const bit [$bits(in_data)-1:0] mem_data;
  endchecker : check
endmodule
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Clocking block parser errors") {
    auto& text = R"(
module m;
    clocking cb @(posedge clk);
        default input output;
        default;
        default inout;
    endclocking

    clocking @(posedge clk); endclocking
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::ExpectedClockingSkew);
    CHECK(diagnostics[1].code == diag::ExpectedClockingSkew);
    CHECK(diagnostics[2].code == diag::ExpectedClockingSkew);
    CHECK(diagnostics[3].code == diag::InOutDefaultSkew);
    CHECK(diagnostics[4].code == diag::ClockingNameEmpty);
}

TEST_CASE("Interconnect net parsing") {
    auto& text = R"(
package NetsPkg;
  nettype real realNet;
endpackage : NetsPkg

module top();
   interconnect [0:1] iBus;
   lDriver l1(iBus[0]);
   rDriver r1(iBus[1]);
   rlMod m1(iBus);
endmodule : top

module lDriver(output wire logic out);
endmodule : lDriver

module rDriver
  import NetsPkg::*;
  (output realNet out);
endmodule : rDriver

module rlMod(input interconnect [0:1] iBus);
  lMod l1(iBus[0]);
  rMod r1(iBus[1]);
endmodule : rlMod
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Net alias parsing") {
    auto& text = R"(
module m;
    alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B = {C, A};
endmodule
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Package export parsing") {
    auto& text = R"(
package p;
    export a::b, a::*;
    export *::*;
endpackage
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Covergroup parsing") {
    auto& text = R"(
class cg_cls;
	covergroup cg (ref logic [0:3] x, ref logic [0:7] y, ref logic [0:2] a);
	    xy: coverpoint {x,y};
	    coverpoint y;
	    XYA: cross xy, a { }
	endgroup
	
	covergroup cg;
	    coverpoint a { bins x[] = {[0:10]}; }
	    coverpoint b { bins y[] = {[0:20]}; }
	    aXb : cross a, b
	    {
	        bins one = '{ '{1,2}, '{3,4}, '{5,6} };
	    }
	endgroup
endclass

module top;
	bit [7:0] v_a, v_b;
	covergroup cg @(posedge clk);
	    a: coverpoint v_a
	    {
		    bins a1 = { [0:63] };
		    bins a2 = { [64:127] };
		    bins a3 = { [128:191] };
		    bins a4 = { [192:255] };
	    }
	    b: coverpoint v_b
	    {
		    bins b1 = {0};
		    bins b2 = { [1:84] };
		    bins b3 = { [85:169] };
		    bins b4 = { [170:255] };
	    }
	    c : cross a, b
	    {
		    bins c1 = ! binsof(a) intersect {[100:200]};
		    bins c2 = binsof(a.a2) || binsof(b.b2);
		    bins c3 = binsof(a.a1) && binsof(b.b4);
	    }
	endgroup
endmodule

module mod_m;
	logic [31:0] a, b;
	covergroup cg(int cg_lim);
	    coverpoint a;
	    coverpoint b;
	    aXb : cross a, b
	    {
		    function CrossQueueType myFunc1(int f_lim);
			    for (int i = 0; i < f_lim; ++i)
			    myFunc1.push_back('{i,i});
		    endfunction
		    bins one = myFunc1(cg_lim);
		    bins two = myFunc2(cg_lim);
		    function CrossQueueType myFunc2(logic [31:0] f_lim);
			    for (logic [31:0] i = 0; i < f_lim; ++i)
			    myFunc2.push_back('{2*i,2*i});
		    endfunction
	    }
	endgroup
	cg cg_inst = new(3);
	
	covergroup yy;
	    cross a, b
	    {
	        ignore_bins ignore = binsof(a) intersect { 5, [1:3] };
	    }
	endgroup
endmodule

covergroup g1 (int w, string instComment) @(posedge clk) ;
    option.per_instance = 1;
    option.comment = instComment;
    a : coverpoint a_var
    { option.auto_bin_max = 128; }
    b : coverpoint b_var { option.weight = w; }
    c1 : cross a_var, b_var ;
endgroup

covergroup sg @(posedge clk);
  coverpoint v
  {
    bins b2 = (2 [-> 3:5] );
    bins b3 = (3[-> 3:5] );
    bins b5 = (5 [* 3] );
    bins b6 = (1 => 2 [= 3:6] => 5);
  }
endgroup
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Package-scoped checker instance parsing") {
    auto& text = R"(
package p;
    checker c; endchecker
endpackage

checker c1; p::c foo(); endchecker

module m;
    $unit::c1 bar();
endmodule
)";

    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}
