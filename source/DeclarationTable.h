#pragma once

#include <unordered_map>

#include "AllSyntax.h"
#include "StringRef.h"

namespace slang {

// The declaration table contains all top level hierarchy declarations, which
// includes modules, interfaces, and programs. It's a lightweight representation
// that facilitates two-pass resolution of actual hierarchy symbols.

class DeclarationTable {
public:
    void addDeclarations(const CompilationUnitSyntax* unit) {
        for (auto member : unit->members) {
            switch (member->kind) {
                case SyntaxKind::ModuleDeclaration:
                case SyntaxKind::InterfaceDeclaration:
                case SyntaxKind::ProgramDeclaration: {
                    // ignore empty names
                    auto name = member->as<ModuleDeclarationSyntax>()->header->name.valueText();
                    if (name)
                        declarations.emplace(name, member);
                    break;
                }
                default:
                    break;
            }
        }
    }

    //SyntaxNode* findDeclaration(StringRef name) const;

private:
    std::unordered_map<StringRef, SyntaxNode*> declarations;
};

}