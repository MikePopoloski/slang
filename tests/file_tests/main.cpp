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

    int errors = 0;
    int files = 0;
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        SyntaxTree tree = SyntaxTree::fromFile(StringRef(p.str()), sourceManager);
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", diagWriter.report(tree.diagnostics()).c_str());
        }
        printf("%s", ((CompilationUnitSyntax*)tree.root())->
            toString(SyntaxToStringFlags::IncludeTrivia).c_str());
        errors += tree.diagnostics().count();
        files++;

        trees.emplace_back(std::move(tree));

        //if (errors > 100)
        //  break;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}
