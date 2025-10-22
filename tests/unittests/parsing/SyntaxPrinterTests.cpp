// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "catch2/catch_test_macros.hpp"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

TEST_CASE("SyntaxPrinter - line comments") {
    auto& cu = parseCompilationUnit(R"(
// This is a leading comment
// for the module
module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    auto leadingComments = SyntaxPrinter().printLeadingComments(module).str();
    auto excludingLeading = SyntaxPrinter().printExcludingLeadingComments(module).str();
    auto withLeading = SyntaxPrinter().printWithLeadingComments(module).str();

    CHECK(leadingComments == "// This is a leading comment\n// for the module\n");
    CHECK(excludingLeading == R"(module m;
endmodule)");
    CHECK(withLeading == leadingComments + excludingLeading);
}

TEST_CASE("SyntaxPrinter - spaced out line comments") {
    auto& cu = parseCompilationUnit(R"(
// This is a also a leading comment
// for the module

module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() ==
          "// This is a also a leading comment\n// for the module\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().setSquashNewlines(false).printWithLeadingComments(module).str() ==
          R"(// This is a also a leading comment
// for the module

module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - block comment") {
    auto& cu = parseCompilationUnit(R"(
/* Not included */
/* Block comment */
module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "/* Block comment */\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(/* Block comment */
module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - double newline boundary") {
    auto& cu = parseCompilationUnit(R"(
// Not a leading comment

// This is a leading comment
module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "// This is a leading comment\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(// This is a leading comment
module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - previous line comment") {
    auto& cu = parseCompilationUnit(R"(
asdf; // Not part of leading comment
// This is a leading comment
module m;
endmodule
)");

    REQUIRE(cu.members.size() >= 2);
    auto& module = cu.members[1]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "// This is a leading comment\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(// This is a leading comment
module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - no leading comment") {
    auto& cu = parseCompilationUnit(R"(
    asdf; // Not part of leading comment
    module m;
    endmodule
)");

    REQUIRE(cu.members.size() >= 2);
    auto& module = cu.members[1]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
    endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(module m;
    endmodule)");
}

TEST_CASE("SyntaxPrinter - no comments") {
    auto& cu = parseCompilationUnit(R"(
module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - start of file") {
    auto& cu = parseCompilationUnit(R"(// This is not a leading comment on the first line
module m;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m;
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(module m;
endmodule)");
}

TEST_CASE("SyntaxPrinter - indented comments") {
    auto& cu = parseCompilationUnit(R"(
module top;
    // Internal comment
    reg x;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();
    auto& body = module.as<ModuleDeclarationSyntax>();
    REQUIRE(body.members.size() > 0);
    auto& reg = *body.members[0];

    // Should not include just whitespace/tabs before the comment
    CHECK(SyntaxPrinter().printLeadingComments(reg).str() ==
          R"(// Internal comment
    )");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(reg).str() == "reg x;");
    CHECK(SyntaxPrinter().printWithLeadingComments(reg).str() ==
          R"(// Internal comment
    reg x;)");
}

TEST_CASE("SyntaxPrinter - indented blank lines") {
    auto& cu = parseCompilationUnit(R"(
module top;


    reg x;
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();
    auto& body = module.as<ModuleDeclarationSyntax>();
    REQUIRE(body.members.size() > 0);
    auto& reg = *body.members[0];

    // Empty lines (whitespace only) should not be considered leading comments
    CHECK(SyntaxPrinter().printLeadingComments(reg).str() == "");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(reg).str() == "reg x;");
    CHECK(SyntaxPrinter().printWithLeadingComments(reg).str() == "reg x;");
}

TEST_CASE("SyntaxPrinter - module with ports") {
    auto& cu = parseCompilationUnit(R"(
// Comment
module m(input a, output b);
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "// Comment\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m(input a, output b);
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(// Comment
module m(input a, output b);
endmodule)");
}

TEST_CASE("SyntaxPrinter - preserves inline comments") {
    auto& cu = parseCompilationUnit(R"(
// Leading comment
module m; // Inline comment
endmodule
)");

    auto& module = cu.members[0]->as<ModuleDeclarationSyntax>();

    CHECK(SyntaxPrinter().printLeadingComments(module).str() == "// Leading comment\n");
    CHECK(SyntaxPrinter().printExcludingLeadingComments(module).str() ==
          R"(module m; // Inline comment
endmodule)");
    CHECK(SyntaxPrinter().printWithLeadingComments(module).str() ==
          R"(// Leading comment
module m; // Inline comment
endmodule)");
}
