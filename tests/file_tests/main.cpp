#include <cstdlib>
#include <string>

#include "slang.h"

using namespace slang;
using namespace std::literals;

static const char RelativeTestPath[] = "../../../tests/file_tests/corpus";

SourceManager sourceManager;

int main() {
    // run through all external files in our corpus and make sure they parse without error
    int errors = 0;
    int files = 0;
    sourceManager.addUserDirectory(RelativeTestPath + "/include"s);
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        SyntaxTree tree = SyntaxTree::fromFile(sourceManager, p.str());
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", tree.diagnostics().reportAll(sourceManager).c_str());
        }

        errors += tree.diagnostics().count();
        files++;

        //if (errors > 100)
        //  break;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}