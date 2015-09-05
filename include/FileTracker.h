#pragma once

namespace slang {

class FileTracker;

struct FileID : public HandleBase<FileID> {
    friend class FileTracker;
};

struct SourceFile {
    Buffer<char> buffer;
    DirectoryID directory;
    FileID file;
};

class FileTracker {
public:
    IFileSystem& fileSystem;

    FileTracker(IFileSystem& fileSystem);

    // tracks a file with the given name, without doing any work to actually open it
    // this can be used to pretend that an in-memory buffer is an actual file somewhere
    FileID track(StringRef path);

    // open a file and load it into memory
    SourceFile open(StringRef path);

    // get the directory ID for the given file ID
    DirectoryID getDirectory(FileID file) const;

private:
    Allocator alloc;
    std::unordered_map<StringRef, FileID> pathMap;
    std::deque<DirectoryID> fileToDirectoryIndex;
    uint32_t nextFileID = 1;
};

}