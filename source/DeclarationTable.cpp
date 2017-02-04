//------------------------------------------------------------------------------
// DeclarationTable.cpp
// Module declaration tracking.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "DeclarationTable.h"

#include <algorithm>

#include "AllSyntax.h"

namespace slang {

DeclarationTable::DeclarationTable(Diagnostics& diagnostics) :
    diagnostics(diagnostics)
{
}

const ModuleDeclarationSyntax* DeclarationTable::find(StringRef name) const {
    auto it = nameLookup.find(name);
    if (it == nameLookup.end())
        return nullptr;
    return it->second.decl;
}

ArrayRef<const ModuleDeclarationSyntax*> DeclarationTable::getTopLevelModules() {
    if (!dirty)
        return ArrayRef<const ModuleDeclarationSyntax*>(topLevel.begin(), topLevel.end());

    topLevel.clear();
    nameLookup.clear();
    dirty = false;

    // merge all module declarations
    for (auto& unit : units) {
        for (const ModuleDeclarationSyntax* node : unit.rootNodes) {
            auto name = node->header->name;
            auto pair = nameLookup.try_emplace(name.valueText(), node);
            if (!pair.second) {
                // report the duplicate name, along with the original location
                diagnostics.add(DiagCode::DuplicateDefinition, name.location()) << StringRef("module") << name.valueText();
                diagnostics.add(DiagCode::NotePreviousDefinition, pair.first->second.decl->header->name.location());
            }
        }
    }

    // figure out which ones are instantiated and error on any that we can't find
    for (auto& unit : units) {
        for (const HierarchyInstantiationSyntax* instantiation : unit.instantiations) {
            auto name = instantiation->type;
            auto it = nameLookup.find(name.valueText());
            if (it == nameLookup.end())
                diagnostics.add(DiagCode::UnknownModule, name.location()) << name.valueText();
            else
                it->second.instantiated = true;
        }
    }

    // finally consolidate the list of top level modules
    for (auto& pair : nameLookup) {
        if (!pair.second.instantiated)
            topLevel.append(pair.second.decl);
    }

    // Sort the top level list so that we remain deterministic (don't rely on hash ordering)
    std::sort(topLevel.begin(), topLevel.end(), [](auto a, auto b) { 
        return a->header->name.valueText() < b->header->name.valueText();
    });

    return ArrayRef<const ModuleDeclarationSyntax*>(topLevel.begin(), topLevel.end());
}

void DeclarationTable::addSyntaxTree(const SyntaxTree* tree) {
    // find all root modules in this compilation unit
    UnitDecls unit;
    for (const MemberSyntax* member : tree->root()->members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                // ignore empty names
                auto decl = member->as<ModuleDeclarationSyntax>();
                auto name = decl->header->name;
                if (name.valueText())
                    unit.rootNodes.push_back(decl);

                std::vector<NameSet> scopeStack;
                visit(decl, unit, scopeStack);
                break;
            }
            default:
                break;
        }
    }
    units.emplace(std::move(unit));
    dirty = true;
}

void DeclarationTable::visit(const ModuleDeclarationSyntax* module, UnitDecls& unit, std::vector<NameSet>& scopeStack) {
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
        visit(member, unit, scopeStack);
    
    if (localDefs)
        scopeStack.pop_back();
}

void DeclarationTable::visit(const MemberSyntax* node, UnitDecls& unit, std::vector<NameSet>& scopeStack) {
    if (!node)
        return;

    switch (node->kind) {
        case SyntaxKind::HierarchyInstantiation: {
            // Determine whether this is a local or global module we're instantiating;
            // don't worry about local instantiations right now, they can't be root.
            auto his = node->as<HierarchyInstantiationSyntax>();
            auto name = his->type.valueText();
            if (name && !containsName(scopeStack, name))
                unit.instantiations.push_back(his);
            break;
        }
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            visit(node->as<ModuleDeclarationSyntax>(), unit, scopeStack);
            break;
        case SyntaxKind::GenerateRegion:
            for (auto& child : node->as<GenerateRegionSyntax>()->members)
                visit(child, unit, scopeStack);
            break;
        case SyntaxKind::GenerateBlock:
            for (auto& child : node->as<GenerateBlockSyntax>()->members)
                visit(child, unit, scopeStack);
            break;
        case SyntaxKind::LoopGenerate:
            visit(node->as<LoopGenerateSyntax>()->block, unit, scopeStack);
            break;
        case SyntaxKind::CaseGenerate:
            for (auto& item : node->as<CaseGenerateSyntax>()->items) {
                switch (item->kind) {
                    case SyntaxKind::DefaultCaseItem:
                        visit(item->as<DefaultCaseItemSyntax>()->clause->as<MemberSyntax>(), unit, scopeStack);
                        break;
                    case SyntaxKind::StandardCaseItem:
                        visit(item->as<StandardCaseItemSyntax>()->clause->as<MemberSyntax>(), unit, scopeStack);
                        break;
                    default:
                        break;
                }
            }
            break;
        case SyntaxKind::IfGenerate: {
            auto ifGen = node->as<IfGenerateSyntax>();
            visit(ifGen->block, unit, scopeStack);
            if (ifGen->elseClause)
                visit(ifGen->elseClause->clause->as<MemberSyntax>(), unit, scopeStack);
            break;
        }
        case SyntaxKind::DefParam:
            // no going back! muahahaha
            unit.hasDefParams = true;
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