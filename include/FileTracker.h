#pragma once

namespace slang {

class FileTracker;

struct FileID : public HandleBase<FileID> {
    friend class FileTracker;
};

struct SourceFile {
    Buffer<char> buffer;
    FileID id;
};

class FileTracker {
public:
    FileTracker();

    // tracks a file with the given name, without doing any work to actually open it
    // this can be used to pretend that an in-memory buffer is an actual file somewhere
    FileID track(StringRef path);

    // open a file and load it into memory
    bool readSource(StringRef path, SourceFile& file);

    // look up and load a header using proper search rules
    // header file source is cached and reused
    SourceFile* readHeader(FileID currentSource, StringRef path, bool systemPath);

private:
    BumpAllocator alloc;
    std::unordered_map<StringRef, FileID> pathMap;
    std::tr2::sys::path workingDir;
    uint32_t nextFileID = 1;

    bool openFile(const std::tr2::sys::path& path, Buffer<char>& buffer);
};

}