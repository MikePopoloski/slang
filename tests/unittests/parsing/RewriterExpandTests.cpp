// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

TEST_CASE("Rewriter expand macros functionality") {
    // Simple test case with inline macro definitions
    auto testText = R"(`define MY_MACRO 42
`define FUNC_MACRO(x) (x + 1)
`define SIMPLE_MACRO 200

module test;
    int a = `MY_MACRO;
    int b = `FUNC_MACRO(5);
    int c = `MY_MACRO + `FUNC_MACRO(10);
    int d = `SIMPLE_MACRO;
endmodule)";

    SECTION("Test expandMacros option") {
        // Parse the test file
        auto tree = SyntaxTree::fromText(testText);
        // Note: root could be CompilationUnit or ModuleDeclaration depending on parsing
        REQUIRE(tree != nullptr);

        // Test with expandMacros enabled
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandMacros(true);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // When macros are expanded, we should see the literal values instead of macro names
        auto expected = R"(`define MY_MACRO 42
`define FUNC_MACRO(x) (x + 1)
`define SIMPLE_MACRO 200
module test;
    int a = 42;
    int b = (5 + 1);
    int c = 42 + (10 + 1);
    int d = 200;
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test expandMacros disabled") {
        // Parse the test file
        auto tree = SyntaxTree::fromText(testText);
        // Note: root could be CompilationUnit or ModuleDeclaration depending on parsing
        REQUIRE(tree != nullptr);

        // Test with expandMacros disabled (default)
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandMacros(false);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // When macros are not expanded, we should see the macro names
        auto expected = R"(`define MY_MACRO 42
`define FUNC_MACRO(x) (x + 1)
`define SIMPLE_MACRO 200
module test;
    int a = `MY_MACRO;
    int b = `FUNC_MACRO(5);
    int c = `MY_MACRO + `FUNC_MACRO(10);
    int d = `SIMPLE_MACRO;
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test macro round trip") {
        // Parse the test file
        auto tree = SyntaxTree::fromText(testText);
        // Note: root could be CompilationUnit or ModuleDeclaration depending on parsing
        REQUIRE(tree != nullptr);

        // Test with expandMacros disabled (default)
        SyntaxPrinter printer(tree->sourceManager());

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // This had issues with a shortcut for printing triva-
        // `FUNC_MACRO(10); would turn into `FUNC_MACRO(10)    ;, since trivia was not handled
        // correctly

        // When macros are not expanded, we should see the macro names
        auto expected = R"(
module test;
    int a = `MY_MACRO;
    int b = `FUNC_MACRO(5);
    int c = `MY_MACRO + `FUNC_MACRO(10);
    int d = `SIMPLE_MACRO;
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test expandIncludes option") {
        // Create a custom SourceManager and add include file content
        SourceManager sourceManager;
        sourceManager.setDisableProximatePaths(true);

        // Add the include file content to SourceManager
        auto includeContent = R"(`define INCLUDED_MACRO 999
`define INCLUDED_FUNC(x) ((x) + 100))";
        sourceManager.assignText("test_header.svh", includeContent);

        // Test case with actual include directive
        auto includeTestText = R"(`include "test_header.svh"

module test;
    int a = `INCLUDED_MACRO;
    int b = `INCLUDED_FUNC(10);
endmodule)";

        // Parse the test file with our custom SourceManager
        auto tree = SyntaxTree::fromText(includeTestText, sourceManager);
        REQUIRE(tree != nullptr);

        // Test with expandIncludes enabled
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandIncludes(true);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // When expandIncludes is true, include directives are EXCLUDED from output
        // The included content is processed but directives themselves are removed
        auto expected = R"(`define INCLUDED_MACRO 999
`define INCLUDED_FUNC(x) ((x) + 100)
module test;
    int a = `INCLUDED_MACRO;
    int b = `INCLUDED_FUNC(10);
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test expandIncludes disabled") {
        // Create a custom SourceManager and add include file content
        SourceManager sourceManager;
        sourceManager.setDisableProximatePaths(true);

        // Add the include file content to SourceManager
        auto includeContent = R"(`define INCLUDED_MACRO 999
`define INCLUDED_FUNC(x) ((x) + 100))";
        sourceManager.assignText("test_header.svh", includeContent);

        // Test case with actual include directive
        auto includeTestText = R"(`include "test_header.svh"

module test;
    int a = `INCLUDED_MACRO;
    int b = `INCLUDED_FUNC(10);
endmodule)";

        // Parse the test file with our custom SourceManager
        auto tree = SyntaxTree::fromText(includeTestText, sourceManager);
        REQUIRE(tree != nullptr);

        // Test with expandIncludes disabled (default)
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandIncludes(false);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // When expandIncludes is false (default), include directives are INCLUDED in output
        auto expected = R"(`include "test_header.svh"
module test;
    int a = `INCLUDED_MACRO;
    int b = `INCLUDED_FUNC(10);
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test both expandMacros and expandIncludes enabled") {
        // Create a custom SourceManager and add include file content
        SourceManager sourceManager;
        sourceManager.setDisableProximatePaths(true);

        // Add the include file content to SourceManager
        auto includeContent = R"(`define INCLUDED_MACRO 777
`define INCLUDED_FUNC(x) ((x) * 2))";
        sourceManager.assignText("test_header.svh", includeContent);

        // Test case combining macro expansion with include expansion
        auto combinedTestText = R"(`define LOCAL_MACRO 555
`include "test_header.svh"

module test;
    int a = `LOCAL_MACRO;
    int b = `INCLUDED_MACRO;
    int c = `INCLUDED_FUNC(5);
endmodule)";

        // Parse the test file with our custom SourceManager
        auto tree = SyntaxTree::fromText(combinedTestText, sourceManager);
        REQUIRE(tree != nullptr);

        // Test with both options enabled
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandIncludes(true);
        printer.setExpandMacros(true);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // Should see expanded macros and included content with include directive removed
        auto expected = R"(`define LOCAL_MACRO 555
`define INCLUDED_MACRO 777
`define INCLUDED_FUNC(x) ((x) * 2)
module test;
    int a = 555;
    int b = 777;
    int c = ((5) * 2);
endmodule)";
        CHECK(resultStr == expected);
    }

    SECTION("Test expandMacros with macro in include") {
        // Create a custom SourceManager and add include file content
        SourceManager sourceManager;
        sourceManager.setDisableProximatePaths(true);

        // Add the include file content to SourceManager
        sourceManager.assignText("test_header.svh", R"(
`define SAFE_DEFINE(__name__, __value__=) \
    `ifndef __name__ \
        `define __name__ __value__ \
    `endif

`SAFE_DEFINE(SOME_VALUE)
)");

        // Test case where with token from macro, but also in include
        auto combinedTestText = R"(
`include "test_header.svh"

module test;
endmodule
)";

        // Parse the test file with our custom SourceManager
        auto tree = SyntaxTree::fromText(combinedTestText, sourceManager);
        REQUIRE(tree != nullptr);

        // Test with both options enabled
        SyntaxPrinter printer(tree->sourceManager());
        printer.setIncludeDirectives(true);
        printer.setExpandMacros(true);

        auto result = printer.print(*tree);
        auto resultStr = result.str();

        // Should not see SOME_VALUE token
        CHECK(resultStr.find("SOME_VALUE") == std::string::npos);
    }
}
