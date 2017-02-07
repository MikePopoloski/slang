#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;

SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        sourceManager = new SourceManager();
        sourceManager->addUserDirectory("tests/unit_tests/data/");
    }
    return *sourceManager;
}

std::string getDiagnostic(int i) {
    return DiagnosticWriter(getSourceManager()).report(diagnostics[i]);
}

Token lexToken(StringRef text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

TEST_CASE("Diagnostic Line Number", "[diagnostic]") {
    auto& text = "`include \"foofile\"\nident";

    // Include a file that doesn't exist, we should still parse the identifier
    // on the next line, but have a diagnostic error on line 1
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "ident");
    CHECK(diagnostics.count() == 1);
    std::string message = getDiagnostic(0);
    int bufNum, line, col;
    sscanf(getDiagnostic(0).c_str(), "<unnamed_buffer%d>:%d:%d", &bufNum, &line, &col);
    CHECK(line == 1);
    CHECK(col == 10);
}


}
