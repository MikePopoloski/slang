#include "slang.h"

namespace slang {

FileTracker::FileTracker(IFileSystem& fileSystem) :
    fileSystem(fileSystem) {
}

FileID FileTracker::track(StringRef path) {
    auto it = pathMap.find(path);
    if (it != pathMap.end())
        return it->second;

    StringRef interned = path.intern(alloc);
    
    FileID result = FileID::get(nextFileID++);
    pathMap[interned] = result;
    fileToDirectoryIndex.push_back(fileSystem.getDeepestDirectory(interned));

    return result;
}

SourceFile FileTracker::open(StringRef fileName) {
    SourceFile result;
    result.file = track(fileName);
    result.directory = getDirectory(result.file);

    fileSystem.readFileAbsolute(fileName, result.buffer);
    return result;
}

DirectoryID FileTracker::getDirectory(FileID file) const {
    return fileToDirectoryIndex[file.getValue()];
}

}