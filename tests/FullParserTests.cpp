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

void parseFile(const SourceFile& file) {
    diagnostics.clear();
	preprocessor.pushSource(file.buffer, file.id);
    Parser parser(preprocessor);

    auto tree = parser.parseCompilationUnit();
    REQUIRE(tree);
	//REQUIRE(tree->toString(SyntaxToStringFlags::IncludeTrivia) == std::string(file.buffer.begin(), file.buffer.end() - 1));
    
	for (auto& diag : diagnostics) {
		auto report = diagnostics.getReport(diag);
		WARN(report.toString());
	}
	
	REQUIRE(diagnostics.empty());
}

TEST_CASE("External files", "[parser:full]") {
    // run through all external files in our corpus and make sure they parse without error
    for (auto& p : fs::directory_iterator(RelativeTestPath)) {
        SourceFile file;
		INFO("Parsing '" + p.path().string() + "'");
        REQUIRE(sourceManager.readSource(p.path().string(), file));
        parseFile(file);
    }
}

}