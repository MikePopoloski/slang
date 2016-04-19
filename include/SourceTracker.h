#pragma once

#include "Handle.h"
#include "SourceLocation.h"

namespace slang {

class SourceTracker;

struct FileID : public HandleBase<FileID> {
    friend class SourceTracker;
};

struct SourceFile {
    Buffer<char> buffer;
    FileID id;

    SourceFile() : buffer(0) {}
    SourceFile(FileID id, Buffer<char>&& buffer) :
        id(id), buffer(std::move(buffer)) {
    }
};

class SourceTracker {
public:
    SourceTracker();

    std::string makeAbsolutePath(StringRef path) const;
    void addSystemDirectory(StringRef path);
    void addUserDirectory(StringRef path);

    // tracks a file with the given name, without doing any work to actually open it
    // this can be used to pretend that an in-memory buffer is an actual file somewhere
    FileID track(StringRef path);

    // open a file and load it into memory
    bool readSource(StringRef path, SourceFile& file);

    // look up and load a header using proper search rules
    // header file source is cached and reused
    SourceFile* readHeader(FileID currentSource, StringRef path, bool systemPath);

private:
    using path_type = std::tr2::sys::path;

    BumpAllocator alloc;
    path_type workingDir;
    uint32_t nextFileID = 1;

    // map from arbitrary string name to file IDs
    std::unordered_map<StringRef, FileID> pathMap;

    // cache for header lookups; this holds on to the actual file data
    std::unordered_map<std::string, std::unique_ptr<SourceFile>> lookupCache;

    // map from FileID to containing directory
    std::deque<const path_type*> fileToDirectory;

    // directories for system and user includes
    std::vector<path_type> systemDirectories;
    std::vector<path_type> userDirectories;

    // uniquified backing memory for directories
    std::set<path_type> directories;

    bool openFile(const path_type& path, Buffer<char>& buffer);
    SourceFile* openCached(path_type fullPath);
    void cacheDirectory(path_type path, FileID file);
};

}