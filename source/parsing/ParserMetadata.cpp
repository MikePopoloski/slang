//------------------------------------------------------------------------------
// ParserMetadata.cpp
// Metadata collected during parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/ParserMetadata.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/FlatMap.h"

namespace slang::parsing {

using namespace syntax;

namespace {

class MetadataVisitor : public SyntaxVisitor<MetadataVisitor> {
public:
    ParserMetadata meta;

    void handle(const CompilationUnitSyntax& syntax) {
        meta.eofToken = syntax.endOfFile;
        visitDefault(syntax);
    }

    void handle(const ScopedNameSyntax& syntax) {
        if (syntax.left->kind == SyntaxKind::IdentifierName &&
            syntax.separator.kind == TokenKind::DoubleColon) {
            meta.classPackageNames.push_back(&syntax.left->as<IdentifierNameSyntax>());
        }
    }

    void handle(const PackageImportDeclarationSyntax& syntax) {
        meta.packageImports.push_back(&syntax);
    }

    void handle(const ClassDeclarationSyntax& syntax) {
        meta.classDecls.push_back(&syntax);
        visitDefault(syntax);
    }

    void handle(const BindDirectiveSyntax& syntax) {
        meta.hasBindDirectives = true;
        visitDefault(syntax);
    }

    void handle(const InterfacePortHeaderSyntax& syntax) {
        std::string_view name = syntax.nameOrKeyword.valueText();
        if (name != "" && name != "interface")
            meta.interfacePorts.push_back(&syntax);
        visitDefault(syntax);
    }

    void handle(const DefParamSyntax& syntax) {
        meta.hasDefparams = true;
        visitDefault(syntax);
    }

    void handle(const HierarchyInstantiationSyntax& syntax) {
        std::string_view name = syntax.type.valueText();
        if (!name.empty() && syntax.type.kind == TokenKind::Identifier) {
            bool found = false;
            for (auto& set : moduleDeclStack) {
                if (set.find(name) != set.end()) {
                    found = true;
                    break;
                }
            }
            if (!found)
                meta.globalInstances.push_back(&syntax);
        }
        visitDefault(syntax);
    }

    void handle(const GenerateBlockSyntax& syntax) {
        moduleDeclStack.emplace_back();
        visitDefault(syntax);
        moduleDeclStack.pop_back();
    }

    void handle(const ModuleDeclarationSyntax& syntax) {
        if (syntax.parent && syntax.parent->kind != SyntaxKind::CompilationUnit) {
            auto name = syntax.header->name.valueText();
            moduleDeclStack.back().emplace(name);
        }

        moduleDeclStack.emplace_back();
        visitDefault(syntax);
        moduleDeclStack.pop_back();

        // Needs to come after we visitDefault because visiting the first token
        // might update our preproc state.
        meta.nodeMeta.emplace_back(&syntax, ParserMetadata::Node{defaultNetType, unconnectedDrive,
                                                                 cellDefine, timeScale});
    }

    void visitToken(Token token) {
        // Look through the token's trivia for any preprocessor directives
        // that might need to be captured in the metadata for module decls.
        for (auto t : token.trivia()) {
            if (t.kind == TriviaKind::Directive) {
                auto s = t.syntax();
                switch (s->kind) {
                    case SyntaxKind::DefaultNetTypeDirective:
                        defaultNetType = s->as<DefaultNetTypeDirectiveSyntax>().netType.kind;
                        if (defaultNetType == TokenKind::Identifier)
                            defaultNetType = TokenKind::Unknown;
                        break;
                    case SyntaxKind::UnconnectedDriveDirective:
                        unconnectedDrive = s->as<UnconnectedDriveDirectiveSyntax>().strength.kind;
                        break;
                    case SyntaxKind::NoUnconnectedDriveDirective:
                        unconnectedDrive = TokenKind::Unknown;
                        break;
                    case SyntaxKind::CellDefineDirective:
                        cellDefine = true;
                        break;
                    case SyntaxKind::EndCellDefineDirective:
                        cellDefine = false;
                        break;
                    case SyntaxKind::TimeScaleDirective: {
                        auto& tsd = s->as<TimeScaleDirectiveSyntax>();
                        if (tsd.timeUnit.kind == TokenKind::TimeLiteral &&
                            tsd.timePrecision.kind == TokenKind::TimeLiteral) {
                            auto unit = TimeScaleValue::fromLiteral(
                                tsd.timeUnit.realValue(), tsd.timeUnit.numericFlags().unit());
                            auto prec = TimeScaleValue::fromLiteral(
                                tsd.timePrecision.realValue(),
                                tsd.timePrecision.numericFlags().unit());

                            if (unit && prec)
                                timeScale = {*unit, *prec};
                        }
                        break;
                    }
                    case SyntaxKind::ResetAllDirective:
                        defaultNetType = TokenKind::Unknown;
                        unconnectedDrive = TokenKind::Unknown;
                        cellDefine = false;
                        timeScale = {};
                        break;
                    default:
                        break;
                }
            }
        }
    }

private:
    SmallVector<flat_hash_set<std::string_view>, 4> moduleDeclStack;
    TokenKind defaultNetType = TokenKind::Unknown;
    TokenKind unconnectedDrive = TokenKind::Unknown;
    bool cellDefine = false;
    std::optional<TimeScale> timeScale;
};

} // namespace

ParserMetadata ParserMetadata::fromSyntax(const SyntaxNode& root) {
    MetadataVisitor visitor;
    root.visit(visitor);
    return visitor.meta;
}

std::vector<std::string_view> ParserMetadata::getDeclaredSymbols() const {
    std::vector<std::string_view> declared;
    visitDeclaredSymbols([&](std::string_view name) { declared.push_back(name); });
    return declared;
}

void ParserMetadata::visitDeclaredSymbols(function_ref<void(std::string_view)> func) const {
    for (auto& [decl, _] : nodeMeta) {
        std::string_view name = decl->header->name.valueText();
        if (!name.empty())
            func(name);
    }

    for (auto classDecl : classDecls) {
        std::string_view name = classDecl->name.valueText();
        if (!name.empty())
            func(name);
    }
}

std::vector<std::string_view> ParserMetadata::getReferencedSymbols() const {
    flat_hash_set<std::string_view> seenDeps;
    std::vector<std::string_view> results;
    visitReferencedSymbols([&](std::string_view name) {
        if (seenDeps.insert(name).second)
            results.push_back(name);
    });
    return results;
}

void ParserMetadata::visitReferencedSymbols(function_ref<void(std::string_view)> func) const {
    for (auto name : globalInstances)
        func(name->type.valueText());

    for (auto idName : classPackageNames) {
        std::string_view name = idName->identifier.valueText();
        if (!name.empty())
            func(name);
    }

    for (auto importDecl : packageImports) {
        for (auto importItem : importDecl->items) {
            std::string_view name = importItem->package.valueText();
            if (!name.empty())
                func(name);
        }
    }

    for (auto intf : interfacePorts) {
        std::string_view name = intf->nameOrKeyword.valueText();
        if (!name.empty())
            func(name);
    }
}

} // namespace slang::parsing
