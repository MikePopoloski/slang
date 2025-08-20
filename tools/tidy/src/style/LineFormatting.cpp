//------------------------------------------------------------------------------
// LineFormatting.cpp
// Check for line length (80 characters max) and tab characters
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace line_formatting {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const RootSymbol& root) {
        // Get all syntax trees and check them
        auto& compilation = root.getCompilation();
        for (const auto& tree : compilation.getSyntaxTrees()) {
            checkSyntaxTree(*tree);
        }
    }

private:
    void checkSyntaxTree(const SyntaxTree& tree) {
        auto& sourceManager = tree.sourceManager();
        // Get the buffer for this syntax tree
        auto location = tree.root().sourceRange().start();
        auto buffer = location.buffer();
        if (!buffer.valid()) {
            return;
        }
        auto text = sourceManager.getSourceText(buffer);
        checkSourceText(text, buffer, sourceManager);
    }
    
    void checkSourceText(std::string_view text, BufferID bufferId, const SourceManager& sourceManager) {
        size_t lineNumber = 1;
        size_t lineStart = 0;
        
        for (size_t i = 0; i <= text.length(); ++i) {
            // Check for end of line or end of file
            if (i == text.length() || text[i] == '\n') {
                // Get the current line content
                std::string_view line = text.substr(lineStart, i - lineStart);
                
                // Check for tab characters
                for (size_t pos = 0; pos < line.length(); ++pos) {
                    if (line[pos] == '\t') {
                        SourceLocation loc(bufferId, lineStart + pos);
                        diags.add(diag::LineFormatting, loc)
                            << "line contains tab character at column " + std::to_string(pos + 1) + 
                               " (use spaces instead for consistency)";
                    }
                }
                
                // Check line length (excluding carriage return if present)
                size_t lineLength = line.length();
                if (lineLength > 0 && line.back() == '\r') {
                    lineLength--; // Don't count carriage return in line length
                }
                
                if (lineLength > 80) {
                    SourceLocation loc(bufferId, lineStart + 80);
                    diags.add(diag::LineFormatting, loc)
                        << "line exceeds 80 characters (length: " + std::to_string(lineLength) + ")";
                }
                
                // Move to next line
                lineNumber++;
                lineStart = i + 1;
            }
        }
    }
};
} // namespace line_formatting

using namespace line_formatting;
class LineFormatting : public TidyCheck {
public:
    [[maybe_unused]] explicit LineFormatting(TidyKind kind,
                                            std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        visitor.handle(root);
        return diagnostics.empty();
    }
    
    DiagCode diagCode() const override { return diag::LineFormatting; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }
    std::string diagString() const override { 
        return "line formatting issue: {}"; 
    }
    std::string name() const override { return "LineFormatting"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces line length (80 characters max) and prohibits tab characters";
    }
};

REGISTER(LineFormatting, LineFormatting, TidyKind::Style)