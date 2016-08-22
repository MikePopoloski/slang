#include "SemanticModel.h"

#include <unordered_map>

#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel(ArrayRef<const SyntaxTree*> syntaxTrees) :
    syntaxTrees(syntaxTrees)
{
    // find all top-level modules
    std::unordered_map<StringRef, SyntaxNode*> topLevelModules;
    for (auto& syntax : syntaxTrees) {
        for (auto& member : syntax->root()->members) {
            switch (member->kind) {
                case SyntaxKind::ModuleDeclaration:
                case SyntaxKind::InterfaceDeclaration:
                case SyntaxKind::ProgramDeclaration: {
                    // ignore empty names
                    auto name = member->as<ModuleDeclarationSyntax>()->header->name.valueText();
                    if (name)
                        topLevelModules.try_emplace(name, member);
                    break;
                }
                default:
                    break;
            }
        }
    }

    // Now build an initial map of the hierarchy. A bunch of things in elaboration require several
    // passes; the idea here is to hit as many of those things as possible in one go. Those include:
    // - Figure out which modules are instantiated (and by extension which are top-level)
    // - Find all defparams
    // - Learn the names and general structure of hierarchy elements. By definition these are:
    //      - module / interface / program instances
    //      - generate blocks
    //      - static tasks and functions
    //      - named begin-end blocks
    //      - named fork-join blocks
    for (auto& syntax : syntaxTrees) {
        discoverHierarchy(syntax->root());
    }
}

void SemanticModel::discoverHierarchy(const CompilationUnitSyntax* node) {
    // descend into modules
    for (auto& member : node->members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration:
                discoverHierarchy(member->as<ModuleDeclarationSyntax>());
                break;
            default:
                break;
        }
    }
}

void SemanticModel::discoverHierarchy(ModuleDeclarationSyntax* node) {
    for (auto& member : node->members) {
        switch (member->kind) {
            case SyntaxKind::HierarchyInstantiation:
                discoverHierarchy(member->as<HierarchyInstantiationSyntax>());
                break;
            case SyntaxKind::TaskDeclaration:
            case SyntaxKind::FunctionDeclaration:
                discoverHierarchy(member->as<FunctionDeclarationSyntax>());
                break;
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration:
                discoverHierarchy(member->as<ModuleDeclarationSyntax>());
                break;
            case SyntaxKind::GenerateRegion:
                discoverHierarchy(member->as<GenerateRegionSyntax>());
                break;
            case SyntaxKind::LoopGenerate:
                discoverHierarchy(member->as<LoopGenerateSyntax>());
                break;
            case SyntaxKind::CaseGenerate:
                discoverHierarchy(member->as<CaseGenerateSyntax>());
                break;
            case SyntaxKind::IfGenerate:
                discoverHierarchy(member->as<IfGenerateSyntax>());
                break;
        }
    }
}

}