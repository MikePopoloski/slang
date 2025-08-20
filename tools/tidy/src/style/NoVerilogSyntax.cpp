// SPDX-License-Identifier: MIT
// 18-341 Custom Rule

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace no_verilog_syntax {

struct VerilogSyntaxVisitor : public SyntaxVisitor<VerilogSyntaxVisitor> {
    void handle(const NetDeclarationSyntax& syntax) {
        if (syntax.netType.valueText() == "wire") {
            foundVerilogSyntax.push_back(
                {syntax.netType.location(), "Use 'logic' instead of 'wire'"});
        }
    }

    void handle(const DataDeclarationSyntax& syntax) {
        if (auto namedType = syntax.type->as_if<NamedTypeSyntax>()) {
            if (auto identifierName = namedType->name->as_if<IdentifierNameSyntax>()) {
                auto typeName = identifierName->identifier.valueText();
                if (typeName == "reg" || typeName == "wire" || typeName == "integer") {
                    foundVerilogSyntax.push_back(
                        {identifierName->sourceRange().start(),
                         "Use 'logic' instead of '" + std::string(typeName) + "'"});
                }
            }
        }

        if (syntax.type->kind == SyntaxKind::RegType) {
            foundVerilogSyntax.push_back(
                {syntax.type->sourceRange().start(), "Use 'logic' instead of 'reg'"});
        }

        if (syntax.type->kind == SyntaxKind::IntegerType) {
            foundVerilogSyntax.push_back(
                {syntax.type->sourceRange().start(), "Use 'int' instead of 'integer'"});
        }
    }

    void handle(const ModuleHeaderSyntax& syntax) {
        if (syntax.ports && syntax.ports->kind == SyntaxKind::NonAnsiPortList) {
            foundVerilogSyntax.push_back(
                {syntax.moduleKeyword.location(),
                 "Use ANSI-style port declarations instead of non-ANSI style"});
        }
    }

public:
    struct VerilogSyntaxIssue {
        SourceLocation location;
        std::string message;
    };
    std::vector<VerilogSyntaxIssue> foundVerilogSyntax;
};

struct VerilogASTVisitor : public ASTVisitor<VerilogASTVisitor, true, true, false, true> {
    explicit VerilogASTVisitor(Diagnostics& diagnostics) : diags(diagnostics) {}

    void handle(const ProceduralBlockSymbol& symbol) {
        if (symbol.procedureKind == ProceduralBlockKind::Always) {
            foundVerilogSyntax.push_back(
                {symbol.location, "Use 'always_comb' or 'always_ff' instead of 'always'"});
        }
    }

public:
    struct VerilogSyntaxIssue {
        SourceLocation location;
        std::string message;
    };
    std::vector<VerilogSyntaxIssue> foundVerilogSyntax;
    Diagnostics& diags;
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (!symbol.getSyntax())
            return;

        VerilogSyntaxVisitor syntaxVisitor;
        symbol.getSyntax()->visit(syntaxVisitor);

        for (const auto& issue : syntaxVisitor.foundVerilogSyntax) {
            diags.add(diag::NoVerilogSyntax, issue.location) << issue.message;
        }

        VerilogASTVisitor astVisitor(diags);
        symbol.visit(astVisitor);

        for (const auto& issue : astVisitor.foundVerilogSyntax) {
            diags.add(diag::NoVerilogSyntax, issue.location) << issue.message;
        }
    }

    void handle(const InstanceSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        const auto& body = symbol.body;

        if (body.getSyntax()) {
            VerilogSyntaxVisitor syntaxVisitor;
            body.getSyntax()->visit(syntaxVisitor);

            for (const auto& issue : syntaxVisitor.foundVerilogSyntax) {
                diags.add(diag::NoVerilogSyntax, issue.location) << issue.message;
            }
        }

        VerilogASTVisitor astVisitor(diags);
        body.visit(astVisitor);

        for (const auto& issue : astVisitor.foundVerilogSyntax) {
            diags.add(diag::NoVerilogSyntax, issue.location) << issue.message;
        }
    }
};
} // namespace no_verilog_syntax

using namespace no_verilog_syntax;
class NoVerilogSyntax : public TidyCheck {
public:
    [[maybe_unused]] explicit NoVerilogSyntax(TidyKind kind,
                                              std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);

        root.visit(visitor);

        auto& compilation = root.getCompilation();
        for (auto syntaxTree : compilation.getSyntaxTrees()) {
            VerilogSyntaxVisitor syntaxVisitor;
            syntaxTree->root().visit(syntaxVisitor);

            for (const auto& issue : syntaxVisitor.foundVerilogSyntax) {
                diagnostics.add(diag::NoVerilogSyntax, issue.location) << issue.message;
            }
        }

        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoVerilogSyntax; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }
    std::string diagString() const override {
        return "use of deprecated Verilog syntax detected: {}";
    }
    std::string name() const override { return "NoVerilogSyntax"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Flags deprecated Verilog syntax and enforces modern SystemVerilog constructs";
    }
};

REGISTER(NoVerilogSyntax, NoVerilogSyntax, TidyKind::Style)
