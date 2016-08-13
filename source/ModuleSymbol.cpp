#include "ModuleSymbol.h"

#include "AllSyntax.h"
#include "DeclarationTable.h"

namespace slang {

ModuleSymbol::ModuleSymbol(const ModuleDeclarationSyntax* syntax, const DeclarationTable& declTable) {
    for (auto& member : syntax->members) {
        switch (member->kind) {
            case SyntaxKind::HierarchyInstantiation:
                handleHierarchyInstantiation(member->as<HierarchyInstantiationSyntax>(), declTable);
                break;
            default:
                break;
        }
    }
}

void ModuleSymbol::handleHierarchyInstantiation(HierarchyInstantiationSyntax* syntax, const DeclarationTable& declTable) {
    // skip if type name is empty; we already reported an error for it
    auto typeName = syntax->type.valueText();
    if (!typeName)
        return;

    if (!declTable.findDeclaration(typeName)) {
        // TODO: error
        return;
    }


}

}