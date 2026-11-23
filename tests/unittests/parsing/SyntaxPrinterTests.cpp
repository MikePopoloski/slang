// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "catch2/catch_test_macros.hpp"
#include <catch2/generators/catch_generators.hpp>

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/text/SourceManager.h"

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

TEST_CASE("SyntaxPrinter line directives preserve source locations") {
    const bool comments = GENERATE(false, true);
    const bool directives = GENERATE(false, true);
    const bool sourceInfo = GENERATE(false, true);
    const auto newline = GENERATE("\n"sv, "\r\n"sv, "\r"sv);

    // Keeps in-memory include lookups from being resolved against the working directory
    SourceManager sourceManager;
    sourceManager.setDisableProximatePaths(true);
    auto withNewlines = [&](std::string_view text) {
        std::string result;
        for (char c : text) {
            if (c == '\n')
                result += newline;
            else
                result += c;
        }
        return result;
    };

    sourceManager.assignText("outer.svh", withNewlines(R"(`line 20 "outer.svh" 0
    initial missing_outer = 1;
`include "inner.svh"
    initial missing_outer_after = 1;
)"));
    sourceManager.assignText("inner.svh", withNewlines(R"(`line 30 "inner.svh" 0
    // Included source
    initial missing_inner = 1;
)"));

    auto tree = SyntaxTree::fromFileInMemory(withNewlines(R"(`line 10 "input.sv" 0
`define REPORT(name) initial \
    // Macro body comment \
    name = 1;
`define EMPTY
`define TRAILING 17 /* end */ \

module top;
    `EMPTY
    /* first

       last */
    `REPORT(missing_macro)
`ifdef OMIT
    initial skipped = 0;
`endif
`include "outer.svh"
    string text = "first\
second";
    initial missing_after = 1;
`line 70 "mapped\\path\"name.sv" 0
    initial missing_mapped = 1;
endmodule
)"),
                                             sourceManager, "input.sv");
    REQUIRE(tree->diagnostics().empty());

    auto output = SyntaxPrinter(sourceManager)
                      .setIncludeComments(comments)
                      .setIncludeDirectives(directives)
                      .setIncludeSource(sourceInfo)
                      .setExpandMacros(true)
                      .setExpandIncludes(true)
                      .setSquashNewlines(false)
                      .setEmitLineDirectives(true)
                      .print(*tree)
                      .str();
    INFO(output);

    SourceManager outputSourceManager;
    auto reparsed = SyntaxTree::fromFileInMemory(output, outputSourceManager, "preprocessed.sv");
    REQUIRE(reparsed->diagnostics().empty());

    auto expected = tree->root().tokens_begin();
    auto actual = reparsed->root().tokens_begin();
    for (; expected != tree->root().tokens_end(); ++expected, ++actual) {
        REQUIRE(actual != reparsed->root().tokens_end());
        CAPTURE(expected->rawText());
        CHECK(actual->kind == expected->kind);
        CHECK(actual->rawText() == expected->rawText());
        CHECK(outputSourceManager.getFileName(actual->location()) ==
              sourceManager.getFileName(expected->location()));
        CHECK(outputSourceManager.getLineNumber(actual->location()) ==
              sourceManager.getLineNumber(expected->location()));
    }
    CHECK(actual == reparsed->root().tokens_end());

    Compilation originalCompilation;
    originalCompilation.addSyntaxTree(tree);
    auto originalDiags = originalCompilation.getAllDiagnostics();
    REQUIRE(originalDiags.size() == 6);

    Compilation outputCompilation;
    outputCompilation.addSyntaxTree(reparsed);
    auto outputDiags = outputCompilation.getAllDiagnostics();
    REQUIRE(outputDiags.size() == originalDiags.size());
    auto locations = [](const auto& diags, const SourceManager& sm) {
        std::vector<std::pair<std::string_view, size_t>> result;
        for (const auto& diagnostic : diags) {
            CHECK(diagnostic.code == diag::UndeclaredIdentifier);
            result.emplace_back(sm.getFileName(diagnostic.location),
                                sm.getLineNumber(diagnostic.location));
        }
        std::ranges::sort(result);
        return result;
    };
    CHECK(locations(outputDiags, outputSourceManager) == locations(originalDiags, sourceManager));

    CHECK(contains(output, "`line 20 \"outer.svh\" 1"));
    CHECK(contains(output, "`line 31 \"inner.svh\" 1"));
    CHECK(contains(output, "`line 22 \"outer.svh\" 2"));
    CHECK(contains(output, "// outer.svh:20\n") == sourceInfo);
    CHECK(contains(output, "// inner.svh:31\n") == sourceInfo);
    CHECK(contains(output, "// outer.svh:22\n") == sourceInfo);
}

TEST_CASE("SyntaxPrinter keeps directive continuations when dropping comments") {
    auto tree = SyntaxTree::fromText(R"(`define DECLARE(name) \
    // Dropped comment \
    logic name;
module m;
endmodule
)");
    REQUIRE(tree->diagnostics().empty());

    auto output = SyntaxPrinter()
                      .setIncludeDirectives(true)
                      .setIncludeComments(false)
                      .setSquashNewlines(false)
                      .print(*tree)
                      .str();
    CHECK(output == R"(`define DECLARE(name) \
    \
    logic name;
module m;
endmodule
)");
}

TEST_CASE("SyntaxPrinter expands conditional directives") {
    auto tree = SyntaxTree::fromText(R"(`timescale 1ns/1ps
`define A
`ifdef A
module a; endmodule
`ifdef B
module b; endmodule
`endif
`else
module c; endmodule
`endif
module d; endmodule
)");
    REQUIRE(tree->diagnostics().empty());

    auto output = SyntaxPrinter()
                      .setIncludeDirectives(true)
                      .setExpandConditionals(true)
                      .print(*tree)
                      .str();
    CHECK(output == R"(`timescale 1ns/1ps
`define A
module a; endmodule
module d; endmodule
)");

    output = SyntaxPrinter()
                 .setIncludeDirectives(true)
                 .setExpandConditionals(true)
                 .setIncludeMacroDefinitions(false)
                 .print(*tree)
                 .str();
    CHECK(output == R"(`timescale 1ns/1ps
module a; endmodule
module d; endmodule
)");
}
