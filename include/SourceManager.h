#pragma once

#include <deque>
#include <filesystem>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "Buffer.h"
#include "BumpAllocator.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

struct SourceBuffer {
    StringRef data;
    BufferID id;

    explicit operator bool() const { return id.valid(); }
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
    StringRef getBufferName(BufferID id);

    // get the buffer for the given file ID
    const Buffer<char>& getBufferMemory(BufferID id);

    // Give ownership of source code to the manager and refer to it by the given path.
    // This method will fail if the given path is already loaded.
    SourceBuffer assignText(StringRef text);
    SourceBuffer assignText(StringRef path, StringRef text);
    SourceBuffer assignBuffer(StringRef path, Buffer<char>&& buffer);

    // get the source buffer for the file at the specified path
    SourceBuffer readSource(StringRef path);
    SourceBuffer readHeader(StringRef path, SourceLocation includedFrom, bool isSystemPath);

private:
    using path_type = std::tr2::sys::path;

    BumpAllocator alloc;
    path_type workingDir;
    uint32_t nextBufferID = 1;
    uint32_t unnamedBufferCount = 0;

    // Stores actual file contents and metadata; only one per loaded file
    struct FileData {
        Buffer<char> mem;
        std::string name;
        std::vector<uint32_t> lineOffsets;
        const path_type* directory;

        FileData(const path_type* directory, const std::string& name, Buffer<char>&& data) :
            directory(directory),
            name(name),
            mem(std::move(data))
        {
        }
    };

    // Stores a pointer to file data along with information about where we included it
    struct FileInfo {
        FileData* data;
        SourceLocation includedFrom;

        FileInfo() {}
        FileInfo(FileData* data, SourceLocation includedFrom) :
            data(data), includedFrom(includedFrom)
        {
        }
    };

    // Instead of a file, this lets a BufferID point to a macro expansion location
    struct ExpansionInfo {
        SourceLocation originalLocation;
        SourceLocation expansionLocationStart;
        SourceLocation expansionLocationEnd;
    };

    // One BufferEntry per BufferID
    struct BufferEntry {
        bool isFile;
        union {
            FileInfo file;
            ExpansionInfo expansion;
        };

        BufferEntry(FileInfo f) : isFile(true), file(f) {}
        BufferEntry(ExpansionInfo e) : isFile(false), expansion(e) {}

        BufferEntry(const BufferEntry& e) {
            isFile = e.isFile;
            if (isFile)
                file = e.file;
            else
                expansion = e.expansion;
        }
    };

    // index from BufferID to buffer metadata
    std::deque<BufferEntry> bufferEntries;

    // cache for file lookups; this holds on to the actual file data
    std::unordered_map<std::string, std::unique_ptr<FileData>> lookupCache;

    // directories for system and user includes
    std::vector<path_type> systemDirectories;
    std::vector<path_type> userDirectories;

    // uniquified backing memory for directories
    std::set<path_type> directories;

    FileData* getFileData(BufferID buffer);
    SourceBuffer createBufferEntry(FileData* fd, SourceLocation includedFrom);

    SourceBuffer openCached(path_type fullPath, SourceLocation includedFrom);
    SourceBuffer cacheBuffer(std::string&& canonicalPath, path_type& path, Buffer<char>&& buffer);

    static void computeLineOffsets(const Buffer<char>& buffer, std::vector<uint32_t>& offsets);
    static bool readFile(const path_type& path, Buffer<char>& buffer);
};

}
