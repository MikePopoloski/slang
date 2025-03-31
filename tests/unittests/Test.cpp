// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include <sstream>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceManager.h"

static std::string findTestDirInternal() {
    auto path = fs::current_path();
    while (!fs::exists(path / "tests")) {
        path = path.parent_path();
        SLANG_ASSERT(!path.empty());
    }

    return (path / "tests/unittests/data/").string();
}

std::string findTestDir() {
    static auto path = findTestDirInternal();
    return path;
}

void setupSourceManager(SourceManager& sourceManager) {
    auto testDir = findTestDir();
    CHECK(!sourceManager.addUserDirectories(testDir));
    CHECK(!sourceManager.addSystemDirectories(testDir));
    CHECK(!sourceManager.addSystemDirectories(testDir + "system/"));
}

SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        auto testDir = findTestDir();
        sourceManager = new SourceManager();
        sourceManager->setDisableProximatePaths(true);
        setupSourceManager(*sourceManager);
    }
    return *sourceManager;
}

bool withinUlp(double a, double b) {
    static_assert(sizeof(double) == sizeof(int64_t));
    int64_t ia, ib;
    memcpy(&ia, &a, sizeof(double));
    memcpy(&ib, &b, sizeof(double));
    return std::abs(ia - ib) <= 1;
}

std::string report(const Diagnostics& diags) {
    if (diags.empty())
        return "";

    return DiagnosticEngine::reportAll(SyntaxTree::getDefaultSourceManager(), diags);
}

std::string reportGlobalDiags() {
    return DiagnosticEngine::reportAll(getSourceManager(), diagnostics);
}

std::string to_string(const Diagnostic& diag) {
    return DiagnosticEngine::reportAll(getSourceManager(), std::span(&diag, 1));
}

Diagnostics filterWarnings(const Diagnostics& diags) {
    Diagnostics results;
    results.reserve(diags.size());

    for (auto& d : diags) {
        if (d.isError())
            results.push_back(d);
    }

    return results;
}

Token lexToken(std::string_view text, LanguageVersion languageVersion) {
    diagnostics.clear();

    auto options = optionsFor(languageVersion);
    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics, options);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

Token lexRawToken(std::string_view text) {
    diagnostics.clear();
    auto& sm = getSourceManager();
    auto buffer = sm.assignText(text);
    Lexer lexer(buffer, alloc, diagnostics, sm);

    Token token = lexer.lex();
    REQUIRE(token);
    return token;
}

const ModuleDeclarationSyntax& parseModule(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    return parser.parseModule().as<ModuleDeclarationSyntax>();
}

const ClassDeclarationSyntax& parseClass(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    return parser.parseClass();
}

const MemberSyntax& parseMember(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    MemberSyntax* member = parser.parseSingleMember(SyntaxKind::ModuleDeclaration);
    REQUIRE(member);
    return *member;
}

const StatementSyntax& parseStatement(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    return parser.parseStatement();
}

const ExpressionSyntax& parseExpression(const std::string& text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Parser parser(preprocessor);
    return parser.parseExpression();
}

Bag optionsFor(LanguageVersion version) {
    PreprocessorOptions ppo;
    ppo.languageVersion = version;

    LexerOptions lo;
    lo.languageVersion = version;

    ParserOptions po;
    po.languageVersion = version;

    CompilationOptions co;
    co.languageVersion = version;

    return {ppo, lo, po, co};
}

const CompilationUnitSyntax& parseCompilationUnit(const std::string& text,
                                                  LanguageVersion languageVersion) {
    diagnostics.clear();

    auto options = optionsFor(languageVersion);
    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics, options);
    preprocessor.pushSource(text);

    Parser parser(preprocessor, options);
    return parser.parseCompilationUnit();
}

const InstanceSymbol& evalModule(std::shared_ptr<SyntaxTree> syntax, Compilation& compilation) {
    compilation.addSyntaxTree(syntax);
    const RootSymbol& root = compilation.getRoot();

    REQUIRE(root.topInstances.size() > 0);
    return *root.topInstances[0];
}

bool LogicExactlyEqualMatcher::match(const logic_t& t) const {
    return exactlyEqual(t, value);
}

std::string LogicExactlyEqualMatcher::describe() const {
    std::ostringstream ss;
    ss << "equals " << value;
    return ss.str();
}

bool SVIntExactlyEqualMatcher::match(const SVInt& t) const {
    return exactlyEqual(t, value);
}

std::string SVIntExactlyEqualMatcher::describe() const {
    std::ostringstream ss;
    ss << "equals " << value;
    return ss.str();
}
