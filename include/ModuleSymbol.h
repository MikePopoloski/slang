#pragma once

namespace slang {

class DeclarationTable;
struct ModuleDeclarationSyntax;
struct HierarchyInstantiationSyntax;

class ModuleSymbol {
public:
    ModuleSymbol(const ModuleDeclarationSyntax* syntax, const DeclarationTable& declTable);

private:
    void handleHierarchyInstantiation(HierarchyInstantiationSyntax* syntax, const DeclarationTable& declTable);
};

}