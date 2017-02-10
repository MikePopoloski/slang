#include <cstdlib>
#include <string>

#include "slang.h"

using namespace slang;
using namespace std::literals;

static const char RelativeTestPath[] = "/Volumes/hrt/surge/testing";

int main() {
    // run through all external files in our corpus and make sure they parse without error
    SourceManager sourceManager;
    sourceManager.addUserDirectory(StringRef("/Volumes/hrt/dev/fpga/include"s));

    DiagnosticWriter diagWriter(sourceManager);
    int errors = 0;
    int files = 0;
    for (auto& p : getFilesInDirectory(RelativeTestPath)) {
        if (p.str().compare(p.str().size() - 3, 3, ".sv")) continue;
        printf("Parsing '%s'\n", p.str().c_str());
        SyntaxTree tree = SyntaxTree::fromFile(StringRef(p.str()), sourceManager);
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.str().c_str());
            printf("%s\n\n", diagWriter.report(tree.diagnostics()).c_str());
        }

        errors += tree.diagnostics().count();
        files++;

        //if (errors > 100)
        //  break;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}
