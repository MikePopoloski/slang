#pragma once

namespace slang {

class Preprocessor {
public:
    Preprocessor(Lexer& lexer, FileTracker& fileTracker);

    void resetAll();
    void include(StringRef path, bool systemPath);
    void define();
    void undefine();
    void undefineAll();
    bool isDefined();
    void setTimescale();
    void setDefaultNetType();
    void startCellTag();
    void endCellTag();
    void beginKeywords();
    void endKeywords();

    FileID getMainFile() const { return mainLexer.getFile(); }
    FileID getCurrentFile() const { return currentLexer ? currentLexer->getFile() : getMainFile(); }

private:
    std::deque<Lexer> lexerStack;
    Lexer& mainLexer;
    Lexer* currentLexer;
    FileTracker& fileTracker;
};

}