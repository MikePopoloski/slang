#pragma once

namespace slang {

class Preprocessor {
public:
    void resetAll();
    void include(StringRef fileName, bool systemPath);
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
};

}