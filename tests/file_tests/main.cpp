#include <cstdlib>
#include <string>

#include "slang.h"

using namespace slang;
using namespace std::literals;

namespace fs = std::tr2::sys;

static const char RelativeTestPath[] = "../../../tests/file_tests/corpus";

BumpAllocator alloc;
Diagnostics diagnostics;
SourceManager sourceManager;
Preprocessor preprocessor(sourceManager, alloc, diagnostics);

int parseFile(const SourceBuffer* buffer, const char* path) {
    diagnostics.clear();
    preprocessor.pushSource(buffer);
    Parser parser(preprocessor);

    auto tree = parser.parseCompilationUnit();
    if (!diagnostics.empty()) {
        printf("Parsing '%s'\n", path);
        for (auto& diag : diagnostics) {
            auto report = diagnostics.getReport(diag);
            printf("%s\n", report.toString(sourceManager).c_str());
        }
        printf("\n\n");
    }
    return diagnostics.count();
}

int main() {
    // run through all external files in our corpus and make sure they parse without error
    int errors = 0;
    int files = 0;
    sourceManager.addUserDirectory(RelativeTestPath + "/include"s);
    for (auto& p : fs::directory_iterator(RelativeTestPath)) {
        if (p.status().type() != fs::file_type::regular)
            continue;

        //if (errors > 100)
            //break;

        auto buffer = sourceManager.readSource(p.path().string());
        errors += parseFile(buffer, p.path().string().c_str());
        files++;
    }

    printf("\n");
    printf("Finished parsing %d files; %d errors found\n\n", files, errors);
}