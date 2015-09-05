#pragma once

namespace slang {

class HeaderSearch {
public:
    // tries to look up and open a header file from a path relative to the given directory
    // lookups are cached internally and reused
    // returns nullptr if file not found
    SourceFile* find(DirectoryID directory, StringRef path);
};

}