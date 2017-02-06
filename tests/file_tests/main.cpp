#include <cstdlib>
#include <string>

#include "slang.h"

using namespace slang;
using namespace std::literals;

static const char RelativeTestPath[] = "tests/file_tests/corpus/include";

int main() {
    // run through all external files in our corpus and make sure they parse without error
    SourceManager sourceManager;
    sourceManager.addUserDirectory(StringRef(RelativeTestPath));

    DiagnosticWriter diagWriter(sourceManager);
    int errors = 0;
    int files = 0;
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        SyntaxTree tree = SyntaxTree::fromFile(sourceManager, StringRef(p.str()));
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", diagWriter.report(tree.diagnostics()).c_str());
        }
        printf("%s", ((CompilationUnitSyntax*)tree.root())->
            toString(SyntaxToStringFlags::IncludeTrivia).c_str());
        errors += tree.diagnostics().count();
        files++;

        //if (errors > 100)
        //  break;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}
