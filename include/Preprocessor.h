#pragma once

namespace slang {

class Preprocessor {
public:
    Preprocessor(FileTracker& fileTracker);

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

    void enterSourceFile(Lexer* lexer);
    Token* next();

    bool hasTokens() const { return currentLexer != nullptr; }
    FileTracker& getFileTracker() const { return fileTracker; }
    FileID getMainFile() const { return mainLexer->getFile(); }
    FileID getCurrentFile() const { return currentLexer ? currentLexer->getFile() : getMainFile(); }

private:
    std::deque<Lexer> lexerStack;
    Lexer* mainLexer;
    Lexer* currentLexer;
    FileTracker& fileTracker;
};

}