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
                 "blah = shortint); endmodule";
    const auto& module = parseModule(text);

    REQUIRE(module.kind == SyntaxKind::ModuleDeclaration);
    CHECK(module.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;

    auto parameters = module.header->parameters->declarations;
    CHECK(parameters[0]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[1]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[2]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[2]->declarators[0]->name.valueText() == "blah");
    CHECK(parameters[3]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[3]->declarators[0]->name.valueText() == "blah");
    CHECK(parameters[3]->declarators[0]->initializer->expr->kind == SyntaxKind::ShortIntType);
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

TEST_CASE("Class members", "[parser:class]") {
    parseClassMember("function void blah(); endfunction", SyntaxKind::ClassMethodDeclaration);
    parseClassMember("virtual function void blah(); endfunction",
                     SyntaxKind::ClassMethodDeclaration);
    parseClassMember("static function type_id blah(); endfunction",
                     SyntaxKind::ClassMethodDeclaration);
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

    auto propertyDecl = parser.parseMember();
    auto coverStatement = parser.parseMember();
    auto assertStatement = parser.parseMember();

    REQUIRE(propertyDecl);
    REQUIRE(coverStatement);
    REQUIRE(assertStatement);
    CHECK_DIAGNOSTICS_EMPTY;
}