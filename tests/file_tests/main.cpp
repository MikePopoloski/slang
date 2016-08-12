#include <cstdlib>
#include <string>

#include "slang.h"

using namespace slang;
using namespace std::literals;

namespace fs = std::tr2::sys;

static const char RelativeTestPath[] = "../../../tests/file_tests/corpus";

SourceManager sourceManager;

int main() {
    // run through all external files in our corpus and make sure they parse without error
    int errors = 0;
    int files = 0;
    sourceManager.addUserDirectory(RelativeTestPath + "/include"s);
    for (auto& p : fs::directory_iterator(RelativeTestPath)) {
        if (p.status().type() != fs::file_type::regular)
            continue;

        //if (errors > 100)
          //  break;

        SyntaxTree tree = SyntaxTree::fromFile(sourceManager, p.path().string());
        if (!tree.diagnostics().empty()) {
            printf("Parsing '%s'\n", p.path().string().c_str());
            printf("%s\n\n", tree.diagnostics().reportAll(sourceManager).c_str());
        }

        errors += tree.diagnostics().count();
        files++;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}