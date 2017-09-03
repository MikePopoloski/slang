#pragma once

#include "Catch/catch.hpp"

#include "diagnostics/Diagnostics.h"
#include "lexing/Preprocessor.h"
#include "parsing/Parser.h"
#include "text/SourceManager.h"
#include "util/BumpAllocator.h"

using namespace slang;

extern BumpAllocator alloc;
extern Diagnostics diagnostics;

#define CHECK_DIAGNOSTICS_EMPTY do {\
    if (!diagnostics.empty()) FAIL_CHECK(DiagnosticWriter(getSourceManager()).report(diagnostics)); \
} while(0)

inline std::string findTestDir() {
    auto path = Path::getCurrentDirectory();
    while (!(path + "tests").exists()) {
        path = path.parentPath();
        ASSERT(!path.empty(), "Failed to find root project directory");
    }

    return (path + "tests/unittests/data/").str();
}

inline SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        auto testDir = findTestDir();
        sourceManager = new SourceManager();
        sourceManager->addUserDirectory(StringRef(testDir));
        sourceManager->addSystemDirectory(StringRef(testDir));
    }
    return *sourceManager;
}

inline bool withinUlp(double a, double b) {
    return std::abs(((int64_t)a - (int64_t)b)) <= 1;
}

inline std::string to_string(const Diagnostic& diag) {
    return DiagnosticWriter(getSourceManager()).report(diag);
}

inline Token lexToken(StringRef text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

inline Token lexRawToken(StringRef text) {
    diagnostics.clear();
    auto buffer = getSourceManager().assignText(text);
    Lexer lexer(buffer, alloc, diagnostics);

    Token token = lexer.lex();
    REQUIRE(token);
    return token;
}

inline const ModuleDeclarationSyntax& parseModule(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(StringRef(text));

    Parser parser(preprocessor);
    return parser.parseModule();
}

inline const ClassDeclarationSyntax& parseClass(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(StringRef(text));

    Parser parser(preprocessor);
    return parser.parseClass();
}

inline const MemberSyntax& parseMember(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(StringRef(text));

    Parser parser(preprocessor);
    MemberSyntax* member = parser.parseMember();
    REQUIRE(member);
    return *member;
}

inline const StatementSyntax& parseStatement(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(StringRef(text));

    Parser parser(preprocessor);
    return parser.parseStatement();
}

inline const ExpressionSyntax& parseExpression(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(StringRef(text));

    Parser parser(preprocessor);
    return parser.parseExpression();
}
