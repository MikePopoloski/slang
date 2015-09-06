#pragma once

namespace slang {

class HeaderSearch {
public:
    // tries to look up and open a header file from a path relative to the given file
    // lookups are cached internally and reused
    // returns nullptr if file not found
    SourceFile* find(FileID currentFile, StringRef path, bool systemPath);
};

}