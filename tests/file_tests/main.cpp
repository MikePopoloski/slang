#include <cstdlib>
#include <string>
#include <vector>

#include "slang.h"

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
    DeclarationTable table {diags};

    int errors = 0;
    int files = 0;
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        SyntaxTree tree = SyntaxTree::fromFile(StringRef(p.str()), sourceManager);
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", diagWriter.report(tree.diagnostics()).c_str());
        }
        //printf("%s", ((CompilationUnitSyntax*)tree.root())->
          //  toString(SyntaxToStringFlags::IncludeTrivia).c_str());
        errors += tree.diagnostics().count();
        files++;

        trees.emplace_back(std::move(tree));
        table.addSyntaxTree(&trees.back());

        if (errors > 100)
            return;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);

    //printf("creating model ...\n");
    BumpAllocator alloc {4096};
    SemanticModel model {alloc, diags, table};

    //printf("iterating over top-level modules:\n");
    int modules = 0;
    for (const auto modulep : table.getTopLevelModules()) {
        //printf("\tinstantiating module %s\n", modulep->header->name.toString().c_str());
        auto inst = model.makeImplicitInstance(modulep);
        modules++;
    }

    printf("\n");
    printf("Finished elaborating %d modules; %d errors found\n\n", modules, errors);
}
