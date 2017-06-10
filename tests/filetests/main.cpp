#include <cstdlib>
#include <string>
#include <vector>

#include "diagnostics/Diagnostics.h"
#include "parsing/SyntaxTree.h"
#include "text/SourceManager.h"

using namespace slang;
using namespace std::literals;

static const char RelativeTestPath[] = "tests/file_tests/corpus/include";

int main() {
    // run through all external files in our corpus and make sure they parse without error
    SourceManager sourceManager;
    sourceManager.addUserDirectory(StringRef(RelativeTestPath));

    DiagnosticWriter diagWriter(sourceManager);
    std::vector<SyntaxTree> trees;
    Diagnostics diags;
    BumpAllocator alloc {4096};
    
    //definitions.addParentScope(model.getSystemScope());

    int errors = 0;
    int files = 0;
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        SyntaxTree tree = SyntaxTree::fromFile(StringRef(p.str()), sourceManager);
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", diagWriter.report(tree.diagnostics()).c_str());
        }
        errors += tree.diagnostics().count();
        files++;

        trees.emplace_back(std::move(tree));
        //table.addSyntaxTree(trees.back());

        if (errors > 100)
            return 1;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);

    // construct a blank interface with empty scope linking to this scope
    // required by SemanticModel::makeInterfacePorts
    // TODO: make un-elaborated InterfaceSymbol/ModuleSymbol as a TypeSymbol and add to definitions scope
    /*for (const auto interfacep : table.getInterfaces()) {
        auto scope = alloc.emplace<Scope>();
        scope->addParentScope(&definitions);
        auto interfaceSym = alloc.emplace<ModuleSymbol>(*interfacep, scope, ArrayRef<const Symbol*>());
        definitions.add(interfaceSym);
    }

    int modules = 0;
    for (const auto modulep : table.getTopLevelModules()) {
        auto inst = model.makeImplicitInstance(*modulep, &definitions);
        modules++;
    }*/

    printf("\n");
    //printf("Finished elaborating %d top-level modules; %d errors found\n\n", modules, errors);
}
