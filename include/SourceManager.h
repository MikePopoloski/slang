#pragma once

#include "SourceLocation.h"

namespace slang {

struct SourceBuffer {
    Buffer<char> data;
    FileID id;

    SourceBuffer() : data(0) {}
    SourceBuffer(FileID id, Buffer<char>&& data) :
        id(id), data(std::move(data)) {
    }
};

class SourceManager {
public:
    SourceManager();

    std::string makeAbsolutePath(StringRef path) const;
    void addSystemDirectory(StringRef path);
    void addUserDirectory(StringRef path);

    // SourceLocation and FileID query methods
    uint32_t getLineNumber(SourceLocation location);
    uint32_t getColumnNumber(SourceLocation location);
    StringRef getFileName(FileID file);

    // get the buffer for the given file ID
    SourceBuffer* getBuffer(FileID id);

    // get the source buffer for the file at the specified path
    SourceBuffer* readSource(StringRef path);
    SourceBuffer* readHeader(StringRef path, FileID includedFrom, bool isSystemPath);

    // Give ownership of source code to the manager and refer to it by the given path.
    // This method will fail if the given path is already loaded.
    SourceBuffer* assignBuffer(StringRef path, Buffer<char>&& buffer);

private:
    using path_type = std::tr2::sys::path;

    BumpAllocator alloc;
    path_type workingDir;
    uint32_t nextFileID = 1;

    struct BufferEntry {
        SourceBuffer* buffer = nullptr;
        const path_type* directory = nullptr;
        std::string name;
        std::vector<uint32_t> lineOffsets;
    };

    // index from FileID to buffer metadata
    std::deque<BufferEntry> bufferEntries;

    // cache for file lookups; this holds on to the actual file data
    std::unordered_map<std::string, std::unique_ptr<SourceBuffer>> lookupCache;

    // directories for system and user includes
    std::vector<path_type> systemDirectories;
    std::vector<path_type> userDirectories;

    // uniquified backing memory for directories
    std::set<path_type> directories;

    FileID assignId(StringRef path);
    SourceBuffer* openCached(path_type fullPath);
    
    static void computeLineOffsets(const Buffer<char>& buffer, std::vector<uint32_t>& offsets);
    static bool readFile(const path_type& path, Buffer<char>& buffer);
};

}