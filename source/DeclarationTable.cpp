#include "DeclarationTable.h"

#include <deque>

#include "AllSyntax.h"

namespace slang {

ArrayRef<ModuleDeclarationSyntax*> DeclarationTable::getTopLevelModules(Diagnostics& diagnostics) {
    if (!dirty)
        return ArrayRef<ModuleDeclarationSyntax*>(topLevelModules.begin(), topLevelModules.end());

    topLevelModules.clear();
    nameLookup.clear();
    dirty = false;

    // merge all module declarations
    for (auto& unit : units) {
        for (auto& node : unit.rootNodes) {
            auto name = node->header->name;
            auto pair = nameLookup.try_emplace(name.valueText(), node);
            if (!pair.second)
                diagnostics.add(DiagCode::ModuleRedefinition, name.location()) << name.valueText();
        }
    }

    // figure out which ones are instantiated and error on any that we can't find
    for (auto& unit : units) {
        for (auto& instantiation : unit.instantiations) {
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
            topLevelModules.append(pair.second.decl);
    }

    return ArrayRef<ModuleDeclarationSyntax*>(topLevelModules.begin(), topLevelModules.end());
}

void DeclarationTable::addSyntaxTree(const SyntaxTree* tree) {
    // find all root modules in this compilation unit
    UnitDecls unit;
    for (auto& member : tree->root()->members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                // ignore empty names
                auto decl = member->as<ModuleDeclarationSyntax>();
                auto name = decl->header->name;
                if (name.valueText())
                    unit.rootNodes.append(decl);

                std::deque<NameList> scopeStack;
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

void DeclarationTable::visit(ModuleDeclarationSyntax* module, UnitDecls& unit, std::deque<NameList>& scopeStack) {
    // first find all local module declarations (most modules probably don't have any nested children)
    std::deque<StringRef>* localDefs = nullptr;
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
                    localDefs->push_back(name);
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
}

void DeclarationTable::visit(MemberSyntax* node, UnitDecls& unit, std::deque<NameList>& scopeStack) {
    if (!node)
        return;

    switch (node->kind) {
        case SyntaxKind::HierarchyInstantiation: {
            // determine whether this is a local or global module we're instantiating
            auto his = node->as<HierarchyInstantiationSyntax>();
            auto name = his->type.valueText();
            if (name && !containsName(scopeStack, name))
                unit.instantiations.append(his);
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

bool DeclarationTable::containsName(const std::deque<NameList>& scopeStack, StringRef name) {
    for (const auto& list : scopeStack) {
        for (const auto& item : list) {
            if (item == name)
                return true;
        }
    }
    return false;
}

}