#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceManager sourceManager;

ModuleDeclarationSyntax* parse(const SourceText& text) {
    diagnostics.clear();

    Preprocessor preprocessor(sourceManager, alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    auto node = parser.parseModule();
    REQUIRE(node);
    return node;
}

TEST_CASE("Simple module", "[parser:modules]") {
    auto& text = "module foo(); endmodule";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Simple interface", "[parser:modules]") {
    auto& text = "interface foo(); endinterface";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::InterfaceDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Simple program", "[parser:modules]") {
    auto& text = "program foo(); endprogram";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ProgramDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Complex header", "[parser:modules]") {
    auto& text = "(* foo = 4 *) macromodule automatic foo import blah::*, foo::bar; #(foo = bar, parameter blah, stuff) (input wire i = 3); endmodule";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
    CHECK(module->attributes.count() == 1);
    CHECK(module->header->imports[0]->items.count() == 2);
    CHECK(module->header->parameters->declarations.count() == 3);
    CHECK(module->header->ports->kind == SyntaxKind::AnsiPortList);
}

TEST_CASE("Parameter ports", "[parser:modules]") {
    auto& text = "module foo #(foo, foo [3:1][9:0] = 4:3:9, parameter blah = blah, localparam type blah = shortint); endmodule";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());

    auto parameters = module->header->parameters->declarations;
    CHECK(parameters[0]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[1]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(parameters[2]->kind == SyntaxKind::ParameterDeclaration);
    CHECK(((ParameterDeclarationSyntax*)parameters[2])->declarator->name->valueText() == "blah");
    CHECK(parameters[3]->kind == SyntaxKind::TypeParameterDeclaration);
    CHECK(((TypeParameterDeclarationSyntax*)parameters[3])->declarator->name->valueText() == "blah");
    CHECK(((TypeParameterDeclarationSyntax*)parameters[3])->declarator->initializer->expr->kind == SyntaxKind::ShortIntType);
}

const MemberSyntax* parseMember(const std::string& text, SyntaxKind kind) {
    auto fullText = "module foo; " + text + " endmodule";
    auto module = parse(fullText);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toString(SyntaxToStringFlags::IncludeTrivia) == fullText);
    CHECK(diagnostics.empty());

    REQUIRE(module->members.count() == 1);
    REQUIRE(module->members[0]->kind == kind);
    return module->members[0];
}

TEST_CASE("Simple members", "[parser:modules]") {
    parseMember("Foo #(stuff) bar(.*), baz(.clock, .rst(rst + 2));", SyntaxKind::HierarchyInstantiation);
    parseMember("timeunit 30ns / 40ns;", SyntaxKind::TimeUnitsDeclaration);
    parseMember("timeprecision 30ns;", SyntaxKind::TimeUnitsDeclaration);
    parseMember("module foo; endmodule", SyntaxKind::ModuleDeclaration);
    parseMember("interface foo; endinterface", SyntaxKind::InterfaceDeclaration);
    parseMember("program foo; endprogram", SyntaxKind::ProgramDeclaration);
    parseMember("generate logic foo = 4; endgenerate", SyntaxKind::GenerateBlock);
    parseMember("initial begin logic foo = 4; end", SyntaxKind::InitialBlock);
    parseMember("final begin logic foo = 4; end", SyntaxKind::FinalBlock);
    parseMember("always @* begin logic foo = 4; end", SyntaxKind::AlwaysBlock);
    parseMember("always_ff @(posedge clk) begin logic foo = 4; end", SyntaxKind::AlwaysFFBlock);
    parseMember("input [31:0] foo, bar;", SyntaxKind::PortDeclaration);
}

}