// SPDX-License-Identifier: MIT
// 18-341 Custom Rule - Constant Formatting

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include <string>
#include <regex>

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace constant_formatting {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const IntegerLiteral& expr) {
        if (auto syntax = expr.syntax; syntax) {
            auto text = SyntaxPrinter().setIncludeTrivia(false).print(*syntax).str();
            auto location = syntax->sourceRange().start();
            
            if (isTimingDelay(expr)) {
                return;
            }
            
            if (isParameterAssignment(expr)) {
                return;
            }
            
            if (std::regex_match(text, std::regex("^[0-9]+$"))) {
                if (text != "0" && text != "1") {
                    diags.add(diag::ConstantFormatting, location) 
                        << "All constants other than 0 and 1 must be sized (e.g., 18'd" + text + " instead of " + text + ")";
                }
                return;
            }
            
            if (std::regex_match(text, std::regex("^'[bBoOdDhH][0-9a-fA-F_]+$"))) {
                diags.add(diag::ConstantFormatting, location) 
                    << "Constants must be sized (e.g., 8" + text + " instead of " + text + ")";
                return;
            }
            
            std::smatch match;
            if (std::regex_match(text, match, std::regex("^([0-9]+)'[bB]([01_]+)$"))) {
                std::string width = match[1].str();
                std::string binary = match[2].str();
                
                std::string cleanBinary = std::regex_replace(binary, std::regex("_"), "");
                
                if (cleanBinary.length() > 4) {
                    if (!isProperlyFormattedBinary(binary)) {
                        std::string properFormat = formatBinaryWithUnderscores(cleanBinary);
                        diags.add(diag::ConstantFormatting, location) 
                            << "Binary constants of more than 4 bits must be separated every 4 places with underscores (e.g., " + 
                               width + "'b" + properFormat + ")";
                    }
                }
            }
        }
    }

private:
    bool isTimingDelay(const IntegerLiteral& expr) {
        if (auto syntax = expr.syntax) {
            auto parent = syntax->parent;
            if (parent && parent->kind == SyntaxKind::DelayControl) {
                return true;
            }
            if (parent && parent->parent && parent->parent->kind == SyntaxKind::DelayControl) {
                return true;
            }
        }
        return false;
    }
    
    bool isParameterAssignment(const IntegerLiteral& expr) {
        if (auto syntax = expr.syntax) {
            auto parent = syntax->parent;
            int depth = 0;
            while (parent && depth < 5) { 
                if (parent->kind == SyntaxKind::ParameterDeclarationStatement ||
                    parent->kind == SyntaxKind::ParameterDeclaration ||
                    parent->kind == SyntaxKind::ParameterPortList) {
                    return true;
                }
                parent = parent->parent;
                depth++;
            }
        }
        return false;
    }

    bool isProperlyFormattedBinary(const std::string& binary) {
        std::string clean = std::regex_replace(binary, std::regex("_"), "");
        std::string expected = formatBinaryWithUnderscores(clean);
        return binary == expected;
    }
    
    std::string formatBinaryWithUnderscores(const std::string& cleanBinary) {
        if (cleanBinary.length() <= 4) {
            return cleanBinary;
        }
        
        std::string result;
        int count = 0;
        
        for (int i = cleanBinary.length() - 1; i >= 0; i--) {
            if (count > 0 && count % 4 == 0) {
                result = "_" + result;
            }
            result = cleanBinary[i] + result;
            count++;
        }
        
        return result;
    }
};
} // namespace constant_formatting

using namespace constant_formatting;
class ConstantFormatting : public TidyCheck {
public:
    [[maybe_unused]] explicit ConstantFormatting(TidyKind kind,
                                                std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::ConstantFormatting; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }
    std::string diagString() const override { 
        return "improper constant formatting: {}"; 
    }
    std::string name() const override { return "ConstantFormatting"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces proper constant formatting: sized constants and binary underscore separation";
    }
};

REGISTER(ConstantFormatting, ConstantFormatting, TidyKind::Style)