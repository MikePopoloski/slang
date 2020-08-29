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

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ImplicitNotAllowed);
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

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::ExpectedToken);
    CHECK(diagnostics[1].code == diag::ExpectedToken);
    CHECK(diagnostics[2].code == diag::ExpectedHierarchicalInstantiation);
    CHECK(diagnostics[3].code == diag::ExpectedHierarchicalInstantiation);
    CHECK(diagnostics[4].code == diag::ExpectedHierarchicalInstantiation);
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

    REQUIRE(diagnostics.size() == 7);
    CHECK(diagnostics[0].code == diag::NotAllowedInInterface);
    CHECK(diagnostics[1].code == diag::NotAllowedInCU);
    CHECK(diagnostics[2].code == diag::NotAllowedInGenerate);
    CHECK(diagnostics[3].code == diag::NotAllowedInModule);
    CHECK(diagnostics[4].code == diag::NotAllowedInProgram);
    CHECK(diagnostics[5].code == diag::NotAllowedInClocking);
    CHECK(diagnostics[6].code == diag::NotAllowedInPackage);
}

TEST_CASE("Task / constructor parse errors") {
    auto& text = R"(
task int t;
endtask

class C;
    task new();
    endtask

    function int new();
    endfunction

    function new::bar();
    endfunction
endclass
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 4);
    CHECK(diagnostics[0].code == diag::TaskReturnType);
    CHECK(diagnostics[1].code == diag::TaskConstructor);
    CHECK(diagnostics[2].code == diag::ConstructorReturnType);
    CHECK(diagnostics[3].code == diag::NewKeywordQualified);
}
