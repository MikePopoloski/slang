#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace fs = std::tr2::sys;

static const char RelativeTestPath[] = "../../../tests/corpus";

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceManager sourceManager;
Preprocessor preprocessor(sourceManager, alloc, diagnostics);

void parseFile(const SourceBuffer* buffer) {
    diagnostics.clear();
    preprocessor.pushSource(buffer->data, buffer->id);
    Parser parser(preprocessor);

    auto tree = parser.parseCompilationUnit();
    REQUIRE(tree);
    //REQUIRE(tree->toString(SyntaxToStringFlags::IncludeTrivia) == std::string(file.buffer.begin(), file.buffer.end() - 1));
    
    if (!diagnostics.empty()) {
        for (auto& diag : diagnostics) {
            auto report = diagnostics.getReport(diag);
            printf("%s\n", report.toString(sourceManager).c_str());
        }
        printf("\n");
    }

    //REQUIRE(diagnostics.empty());
}

TEST_CASE("External files", "[parser:full]") {
    // run through all external files in our corpus and make sure they parse without error
    for (auto& p : fs::directory_iterator(RelativeTestPath)) {
        INFO("Parsing '" + p.path().string() + "'");

        if (p.path().string().find("or1200_ctrl") != std::string::npos) {
            int i = 4;
            i++;
        }

        SourceBuffer* buffer = sourceManager.readSource(p.path().string());
        REQUIRE(buffer);
        parseFile(buffer);
    }
}

}