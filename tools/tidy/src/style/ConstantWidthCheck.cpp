//------------------------------------------------------------------------------
// ConstantWidthCheck.cpp
// Check that constants fit within their declared bit width
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/AllSyntax.h"
#include <regex>
#include <string>
#include <cctype>

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace constant_width_check {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const IntegerLiteral& literal) {
        if (auto syntax = literal.syntax) {
            auto text = SyntaxPrinter().setIncludeTrivia(false).print(*syntax).str();
            
            std::regex sized_pattern("^([0-9]+)'([bBoOdDhH])(.+)$");
            std::smatch match;
            
            if (std::regex_match(text, match, sized_pattern)) {
                int declaredWidth = std::stoi(match[1].str());
                char base = std::tolower(match[2].str()[0]);
                std::string valueStr = match[3].str();
                
                if (declaredWidth >= 64 || declaredWidth <= 0) {
                    return;
                }
                
                try {
                    uint64_t originalValue = parseValueByBase(valueStr, base);
                    uint64_t maxVal = (1ULL << declaredWidth) - 1;
                    
                    if (originalValue > maxVal) {
                        diags.add(diag::ConstantWidthCheck, literal.sourceRange)
                            << std::string("constant value ") + std::to_string(originalValue) + 
                               " in '" + text + "' overflows " + std::to_string(declaredWidth) + 
                               "-bit width (max value: " + std::to_string(maxVal) + ")";
                    }
                } catch (...) {
                    return;
                }
            }
        }
    }

private:
    uint64_t parseValueByBase(const std::string& valueStr, char base) {
        switch (base) {
            case 'b':
                return std::stoull(valueStr, nullptr, 2);
            case 'o': 
                return std::stoull(valueStr, nullptr, 8);
            case 'd': 
                return std::stoull(valueStr, nullptr, 10);
            case 'h': 
                return std::stoull(valueStr, nullptr, 16);
            default:
                throw std::invalid_argument("Unknown base");
        }
    }
};
} // namespace constant_width_check

using namespace constant_width_check;
class ConstantWidthCheck : public TidyCheck {
public:
    [[maybe_unused]] explicit ConstantWidthCheck(TidyKind kind,
                                                std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }
    
    DiagCode diagCode() const override { return diag::ConstantWidthCheck; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }
    std::string diagString() const override { 
        return "constant range check: {}"; 
    }
    std::string name() const override { return "ConstantWidthCheck"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Checks that constants fit within their declared bit width";
    }
};

REGISTER(ConstantWidthCheck, ConstantWidthCheck, TidyKind::Style)