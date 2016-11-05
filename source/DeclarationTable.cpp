//------------------------------------------------------------------------------
// DeclarationTable.cpp
// Module declaration tracking.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "DeclarationTable.h"

#include "AllSyntax.h"
#include "Symbol.h"

namespace slang {

DeclarationTable::DeclarationTable(ArrayRef<CompilationUnitSymbol*> compilationUnits, Diagnostics& diagnostics) {
    // merge all top level modules
    for (CompilationUnitSymbol* unit : compilationUnits) {
        for (DesignElementSymbol* element : unit->elements) {
            auto pair = nameLookup.try_emplace(element->name, element);
            if (!pair.second) {
                // report the duplicate name, along with the original location
                diagnostics.add(DiagCode::DuplicateModule, element->location) << element->name;
                diagnostics.add(DiagCode::NotePreviousDefinition, pair.first->second->location);
            }
        }
    }

    // find which modules are instantiated
    for (CompilationUnitSymbol* unit : compilationUnits) {
        for (DesignElementSymbol* element : unit->elements) {
            std::vector<NameSet> scopeStack;
            visit(element->syntax, scopeStack);
        }
    }
}

DesignElementSymbol* DeclarationTable::findSymbol(StringRef name) const {
    auto it = nameLookup.find(name);
    if (it == nameLookup.end())
        return nullptr;
    return it->second;
}

void DeclarationTable::visit(const ModuleDeclarationSyntax* module, std::vector<NameSet>& scopeStack) {
    // first find all local module declarations (most modules probably don't have any nested children)
    NameSet* localDefs = nullptr;
    for (auto& member : module->members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                // ignore empty names
                auto name = member->as<ModuleDeclarationSyntax>()->header->name.valueText();
                if (name) {
                    // create new scope entry lazily
                    if (!localDefs) {
                        scopeStack.emplace_back();
                        localDefs = &scopeStack.back();
                    }
                    localDefs->insert(name);
                }
                break;
            }
            default:
                break;
        }
    }

    // now traverse all children
    for (auto& member : module->members)
        visit(member, scopeStack);
    
    if (localDefs)
        scopeStack.pop_back();
}

void DeclarationTable::visit(const MemberSyntax* node, std::vector<NameSet>& scopeStack) {
    if (!node)
        return;

    switch (node->kind) {
        case SyntaxKind::HierarchyInstantiation: {
            // Determine whether this is a local or global module we're instantiating;
            // don't worry about local instantiations right now, they can't be root.
            auto his = node->as<HierarchyInstantiationSyntax>();
            auto name = his->type.valueText();
            if (name && !containsName(scopeStack, name)) {
                auto it = nameLookup.find(name);
                if (it != nameLookup.end())
                    it->second->isReferenced = true;
            }
            break;
        }
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            visit(node->as<ModuleDeclarationSyntax>(), scopeStack);
            break;
        case SyntaxKind::GenerateRegion:
            for (auto& child : node->as<GenerateRegionSyntax>()->members)
                visit(child, scopeStack);
            break;
        case SyntaxKind::GenerateBlock:
            for (auto& child : node->as<GenerateBlockSyntax>()->members)
                visit(child, scopeStack);
            break;
        case SyntaxKind::LoopGenerate:
            visit(node->as<LoopGenerateSyntax>()->block, scopeStack);
            break;
        case SyntaxKind::CaseGenerate:
            for (auto& item : node->as<CaseGenerateSyntax>()->items) {
                switch (item->kind) {
                    case SyntaxKind::DefaultCaseItem:
                        visit(item->as<DefaultCaseItemSyntax>()->clause->as<MemberSyntax>(), scopeStack);
                        break;
                    case SyntaxKind::StandardCaseItem:
                        visit(item->as<StandardCaseItemSyntax>()->clause->as<MemberSyntax>(), scopeStack);
                        break;
                    default:
                        break;
                }
            }
            break;
        case SyntaxKind::IfGenerate: {
            auto ifGen = node->as<IfGenerateSyntax>();
            visit(ifGen->block, scopeStack);
            if (ifGen->elseClause)
                visit(ifGen->elseClause->clause->as<MemberSyntax>(), scopeStack);
            break;
        }
        case SyntaxKind::DefParam:
            // no going back! muahahaha
            hasDefParams = true;
            break;
        default:
            break;
    }
}

bool DeclarationTable::containsName(const std::vector<NameSet>& scopeStack, StringRef name) {
    for (const auto& set : scopeStack) {
        if (set.find(name) != set.end())
            return true;
    }
    return false;
}

}