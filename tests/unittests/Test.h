#pragma once

#include <sstream>

#include "Catch/catch.hpp"

#include "binding/Expressions.h"
#include "binding/Statements.h"
#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "lexing/Preprocessor.h"
#include "parsing/Parser.h"
#include "parsing/SyntaxTree.h"
#include "text/SourceManager.h"
#include "util/BumpAllocator.h"

namespace slang {

extern BumpAllocator alloc;
extern Diagnostics diagnostics;

}

using namespace slang;

#define CHECK_DIAGNOSTICS_EMPTY do {\
    if (!diagnostics.empty()) FAIL_CHECK(DiagnosticWriter(getSourceManager()).report(diagnostics)); \
} while (0)

#define NO_COMPILATION_ERRORS do {\
    if (!compilation.diagnostics().empty()) FAIL_CHECK(DiagnosticWriter(SyntaxTree::getDefaultSourceManager()).report(compilation.diagnostics())); \
} while (0)

inline std::string findTestDir() {
    auto path = Path::getCurrentDirectory();
    while (!(path + "tests").exists()) {
        path = path.parentPath();
        ASSERT(!path.empty());
    }

    return (path + "tests/unittests/data/").str();
}

inline SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        auto testDir = findTestDir();
        sourceManager = new SourceManager();
        sourceManager->addUserDirectory(string_view(testDir));
        sourceManager->addSystemDirectory(string_view(testDir));
    }
    return *sourceManager;
}

inline bool withinUlp(double a, double b) {
    static_assert(sizeof(double) == sizeof(int64_t));
    int64_t ia, ib;
    memcpy(&ia, &a, sizeof(double));
    memcpy(&ib, &b, sizeof(double));
    return std::abs(ia - ib) <= 1;
}

inline std::string to_string(const Diagnostic& diag) {
    return DiagnosticWriter(getSourceManager()).report(diag);
}

inline Token lexToken(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

inline Token lexRawToken(string_view text, LexerMode mode = LexerMode::Normal) {
    diagnostics.clear();
    auto buffer = getSourceManager().assignText(text);
    Lexer lexer(buffer, alloc, diagnostics);

    Token token = lexer.lex(mode);
    REQUIRE(token);
    return token;
}

inline const ModuleDeclarationSyntax& parseModule(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);
    return parser.parseModule();
}

inline const ClassDeclarationSyntax& parseClass(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);
    return parser.parseClass();
}

inline const MemberSyntax& parseMember(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);
    MemberSyntax* member = parser.parseMember();
    REQUIRE(member);
    return *member;
}

inline const StatementSyntax& parseStatement(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);
    return parser.parseStatement();
}

inline const ExpressionSyntax& parseExpression(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(string_view(text));

    Parser parser(preprocessor);
    return parser.parseExpression();
}

inline const ModuleInstanceSymbol& evalModule(std::shared_ptr<SyntaxTree> syntax, Compilation& compilation) {
    compilation.addSyntaxTree(syntax);
    const RootSymbol& root = compilation.getRoot();

    REQUIRE(root.topInstances.size() > 0);
    if (!syntax->diagnostics().empty())
        WARN(syntax->reportDiagnostics());

    return *root.topInstances[0];
}

class LogicExactlyEqualMatcher : public Catch::MatcherBase<logic_t> {
public:
    explicit LogicExactlyEqualMatcher(logic_t v) : value(v) {}

    bool match(const logic_t& t) const override final { return exactlyEqual(t, value); }

    std::string describe() const override final {
        std::ostringstream ss;
        ss << "equals " << value;
        return ss.str();
    }

private:
    logic_t value;
};

inline LogicExactlyEqualMatcher exactlyEquals(logic_t v) {
    return LogicExactlyEqualMatcher(v);
}

class SVIntExactlyEqualMatcher : public Catch::MatcherBase<SVInt> {
public:
    explicit SVIntExactlyEqualMatcher(SVInt v) : value(v) {}

    bool match(const SVInt& t) const override final { return exactlyEqual(t, value); }

    std::string describe() const override final {
        std::ostringstream ss;
        ss << "equals " << value;
        return ss.str();
    }

private:
    SVInt value;
};

inline SVIntExactlyEqualMatcher exactlyEquals(SVInt v) {
    return SVIntExactlyEqualMatcher(v);
}
