// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#pragma once

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning( \
        disable : 4459) // annoying warning about global "alloc" being shadowed by locals
#endif

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_templated.hpp>
#include <filesystem>

#include "slang/ast/Compilation.h"
#include "slang/diagnostics/AllDiags.h"
#include "slang/syntax/SyntaxTree.h"

namespace fs = std::filesystem;

namespace slang {

extern BumpAllocator alloc;
extern Diagnostics diagnostics;

namespace syntax {

struct ClassDeclarationSyntax;
struct CompilationUnitSyntax;
struct ExpressionSyntax;
struct MemberSyntax;
struct ModuleDeclarationSyntax;
struct StatementSyntax;

} // namespace syntax

namespace ast {
class InstanceSymbol;
}

} // namespace slang

using namespace slang;
using namespace slang::parsing;
using namespace slang::syntax;
using namespace slang::ast;

#define CHECK_DIAGNOSTICS_EMPTY               \
    do {                                      \
        diagnostics.sort(getSourceManager()); \
        if (!diagnostics.empty())             \
            FAIL_CHECK(reportGlobalDiags());  \
    } while (0)

#define NO_COMPILATION_ERRORS                          \
    do {                                               \
        auto& diags = compilation.getAllDiagnostics(); \
        if (!diags.empty()) {                          \
            FAIL_CHECK(report(diags));                 \
        }                                              \
    } while (0)

#define NO_SESSION_ERRORS                                                      \
    do {                                                                       \
        auto diags = session.getDiagnostics();                                 \
        if (std::ranges::any_of(diags, [](auto& d) { return d.isError(); })) { \
            FAIL_CHECK(report(diags));                                         \
        }                                                                      \
    } while (0)

std::string findTestDir();
void setupSourceManager(SourceManager& sourceManager);
SourceManager& getSourceManager();

bool withinUlp(double a, double b);

std::string report(const Diagnostics& diags);
std::string reportGlobalDiags();
std::string to_string(const Diagnostic& diag);

Diagnostics filterWarnings(const Diagnostics& diags);

Token lexToken(std::string_view text,
               LanguageVersion languageVersion = LanguageVersion::v1800_2017);
Token lexRawToken(std::string_view text);

Bag optionsFor(LanguageVersion version);

const ModuleDeclarationSyntax& parseModule(const std::string& text);
const ClassDeclarationSyntax& parseClass(const std::string& text);
const MemberSyntax& parseMember(const std::string& text);
const StatementSyntax& parseStatement(const std::string& text);
const ExpressionSyntax& parseExpression(const std::string& text);
const CompilationUnitSyntax& parseCompilationUnit(
    const std::string& text, LanguageVersion languageVersion = LanguageVersion::v1800_2017);
const InstanceSymbol& evalModule(std::shared_ptr<SyntaxTree> syntax, Compilation& compilation);

class LogicExactlyEqualMatcher : public Catch::Matchers::MatcherGenericBase {
public:
    explicit LogicExactlyEqualMatcher(logic_t v) : value(v) {}

    bool match(const logic_t& t) const;
    std::string describe() const final;

private:
    logic_t value;
};

inline LogicExactlyEqualMatcher exactlyEquals(logic_t v) {
    return LogicExactlyEqualMatcher(v);
}

class SVIntExactlyEqualMatcher : public Catch::Matchers::MatcherGenericBase {
public:
    explicit SVIntExactlyEqualMatcher(SVInt v) : value(v) {}

    bool match(const SVInt& t) const;
    std::string describe() const final;

private:
    SVInt value;
};

inline SVIntExactlyEqualMatcher exactlyEquals(SVInt v) {
    return SVIntExactlyEqualMatcher(v);
}
