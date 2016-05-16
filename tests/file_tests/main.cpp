#include <cstdlib>

#include "slang.h"

using namespace slang;

namespace fs = std::tr2::sys;

static const char RelativeTestPath[] = "../../../tests/file_tests/corpus";

BumpAllocator alloc;
Diagnostics diagnostics;
SourceManager sourceManager;
Preprocessor preprocessor(sourceManager, alloc, diagnostics);

void parseFile(const SourceBuffer* buffer) {
    diagnostics.clear();
    preprocessor.pushSource(buffer->data, buffer->id);
    Parser parser(preprocessor);

    auto tree = parser.parseCompilationUnit();
    if (!diagnostics.empty()) {
        for (auto& diag : diagnostics) {
            auto report = diagnostics.getReport(diag);
            printf("%s\n", report.toString(sourceManager).c_str());
        }
        printf("\n");
    }
}

int main() {
    // run through all external files in our corpus and make sure they parse without error
    for (auto& p : fs::directory_iterator(RelativeTestPath)) {
        printf("Parsing '%s'\n", p.path().string().c_str());

        auto buffer = sourceManager.readSource(p.path().string());
        parseFile(buffer);
        printf("\n");
    }
}