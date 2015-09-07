#include "catch.hpp"
#include "slang.h"

using namespace slang;

static BumpAllocator alloc;
static Diagnostics diagnostics;

FileTracker& getTracker() {
    static FileTracker* tracker = nullptr;
    if (!tracker) {
        tracker = new FileTracker();
        tracker->addUserDirectory("../../../tests/data/");
    }
    return *tracker;
}

//const Token& lexToken(Preprocessor& preprocessor, const std::string& text) {
//    diagnostics.clear();
//    Lexer lexer(text, preprocessor, alloc, diagnostics);
//    preprocessor.enterSourceFile(&lexer);
//
//    Token* token = lexer.lex();
//    REQUIRE(token != nullptr);
//    return *token;
//}
//
//TEST_CASE("Include directive", "[preprocessor]") {
//    Preprocessor pp(getTracker());
//
//    auto text = "`include \"include.svh\"";
//    auto token = lexToken(pp, text);
//}