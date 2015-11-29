#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;
Preprocessor preprocessor(sourceTracker, alloc, diagnostics);

ModuleDeclarationSyntax* parse(const SourceText& text) {
    diagnostics.clear();
    Lexer lexer(FileID(), text, preprocessor);
    Parser parser(lexer);

    auto node = parser.parseModule();
    REQUIRE(node);
    return node;
}

TEST_CASE("Simple module", "[parser:modules]") {
    auto& text = "module foo(); endmodule";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toFullString() == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Simple interface", "[parser:modules]") {
    auto& text = "interface foo(); endinterface";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::InterfaceDeclaration);
    CHECK(module->toFullString() == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Simple program", "[parser:modules]") {
    auto& text = "program foo(); endprogram";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ProgramDeclaration);
    CHECK(module->toFullString() == text);
    CHECK(diagnostics.empty());
    CHECK(module->header->name->valueText() == "foo");
}

TEST_CASE("Complex header", "[parser:modules]") {
    auto& text = "(* foo = 4 *) macromodule automatic foo import blah::*, foo::bar; #(foo = bar, parameter blah, stuff) (input wire i = 3); endmodule";
    auto module = parse(text);

    REQUIRE(module->kind == SyntaxKind::ModuleDeclaration);
    CHECK(module->toFullString() == text);
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
    CHECK(module->toFullString() == text);
    CHECK(diagnostics.empty());

    auto parameters = module->header->parameters->declarations;
    CHECK(parameters[0]->kind == SyntaxKind::ParameterAssignment);
}

}