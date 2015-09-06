#include "slang.h"

namespace slang {

HeaderSearch::HeaderSearch(FileTracker& fileTracker) :
    fileTracker(fileTracker) {
}

SourceFile* HeaderSearch::find(FileID currentFile, StringRef path, bool systemPath) {
    // if we have an absolute path, we'll do a straight file load
    if (fileTracker.getFileSystem().isPathAbsolute(path))
        return &fileTracker.open(path);

    // otherwise, load relative to the current file, or any of our search paths


    return nullptr;
}

SourceFile* HeaderSearch::findRelative(DirectoryID directory, StringRef path) {
    return nullptr;
}

}