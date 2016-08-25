#include "SemanticModel.h"

#include <unordered_map>

#include "SyntaxTree.h"

namespace slang {

void SemanticModel::discoverHierarchy(ArrayRef<const SyntaxTree*> syntaxTrees) {
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
        for (auto& member : syntax->root()->members)
            discoverHierarchy(member);
    }
}

SemanticModel::InitialHierarchyNode SemanticModel::discoverHierarchy(HierarchyInstantiationSyntax* node, DeclarationTable& declTable) {
    if (!node)
        return nullptr;

    node->type

    return InitialHierarchyNode(
}

void SemanticModel::discoverHierarchy(FunctionDeclarationSyntax* node) {
}

void SemanticModel::discoverHierarchy(BlockStatementSyntax* node) {
}

void SemanticModel::discoverHierarchy(DefParamSyntax* node) {
}

void SemanticModel::discoverHierarchy(MemberSyntax* node) {
    if (!node)
        return;

    switch (node->kind) {
        case SyntaxKind::HierarchyInstantiation:
            discoverHierarchy(node->as<HierarchyInstantiationSyntax>());
            break;
        case SyntaxKind::TaskDeclaration:
        case SyntaxKind::FunctionDeclaration:
            discoverHierarchy(node->as<FunctionDeclarationSyntax>());
            break;
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            for (auto& child : node->as<ModuleDeclarationSyntax>()->members)
                discoverHierarchy(child);
            break;
        case SyntaxKind::GenerateRegion:
            for (auto& child : node->as<GenerateRegionSyntax>()->members)
                discoverHierarchy(child);
            break;
        case SyntaxKind::GenerateBlock:
            for (auto& child : node->as<GenerateBlockSyntax>()->members)
                discoverHierarchy(child);
            break;
        case SyntaxKind::LoopGenerate:
            discoverHierarchy(node->as<LoopGenerateSyntax>()->block);
            break;
        case SyntaxKind::CaseGenerate:
            for (auto& item : node->as<CaseGenerateSyntax>()->items) {
                switch (item->kind) {
                    case SyntaxKind::DefaultCaseItem:
                        discoverHierarchy(item->as<DefaultCaseItemSyntax>()->clause->as<MemberSyntax>());
                        break;
                    case SyntaxKind::StandardCaseItem:
                        discoverHierarchy(item->as<StandardCaseItemSyntax>()->clause->as<MemberSyntax>());
                        break;
                    default:
                        break;
                }
            }
            break;
        case SyntaxKind::IfGenerate: {
            auto ifGen = node->as<IfGenerateSyntax>();
            discoverHierarchy(ifGen->block);
            if (ifGen->elseClause)
                discoverHierarchy(ifGen->elseClause->clause->as<MemberSyntax>());
            break;
        }
        case SyntaxKind::DefParam:
            discoverHierarchy(node->as<DefParamSyntax>());
            break;
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysLatchBlock:
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock: {
            auto statement = node->as<ProceduralBlockSyntax>()->statement;
            switch (statement->kind) {
                case SyntaxKind::SequentialBlockStatement:
                case SyntaxKind::ParallelBlockStatement:
                    discoverHierarchy(statement->as<BlockStatementSyntax>());
                    break;
                default:
                    break;
            }
            break;
        }
        default:
            break;
    }
}

}