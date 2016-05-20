#include "SourceManager.h"

#include <fstream>

namespace fs = std::tr2::sys;

namespace slang {

SourceManager::SourceManager() {
    workingDir = fs::current_path();

    // add a dummy entry to the start of the directory list so that our file IDs line up
    bufferEntries.push_back({});
}

std::string SourceManager::makeAbsolutePath(StringRef path) const {
    if (!path)
        return "";

    return (workingDir / path_type(path.begin(), path.end())).string();
}

void SourceManager::addSystemDirectory(StringRef path) {
    path_type p = fs::absolute(path_type(path.begin(), path.end()), workingDir);
    systemDirectories.push_back(fs::canonical(p));
}

void SourceManager::addUserDirectory(StringRef path) {
    path_type p = fs::absolute(path_type(path.begin(), path.end()), workingDir);
    userDirectories.push_back(fs::canonical(p));
}

uint32_t SourceManager::getLineNumber(SourceLocation location) {
    if (!location.file)
        return 0;

    ASSERT(location.file.id < bufferEntries.size());
    BufferEntry& entry = bufferEntries[location.file.id];

    // compute line offsets if we haven't already
    if (entry.lineOffsets.empty())
        computeLineOffsets(entry.buffer->data, entry.lineOffsets);

    auto it = std::lower_bound(entry.lineOffsets.begin(), entry.lineOffsets.end(), location.offset);
    return (uint32_t)(it - entry.lineOffsets.begin());
}

uint32_t SourceManager::getColumnNumber(SourceLocation location) {
    if (!location.file)
        return 0;

    ASSERT(location.file.id < bufferEntries.size());
    BufferEntry& entry = bufferEntries[location.file.id];
    Buffer<char>& data = entry.buffer->data;

    // walk backward to find start of line
    uint32_t lineStart = location.offset;
    ASSERT(lineStart < data.count());
    while (lineStart > 0 && data[lineStart - 1] != '\n' && data[lineStart - 1] != '\r')
        lineStart--;

    return location.offset - lineStart + 1;
}

StringRef SourceManager::getFileName(FileID file) {
    if (!file)
        return nullptr;

    ASSERT(file.id < bufferEntries.size());
    return bufferEntries[file.id].name;
}

SourceBuffer* SourceManager::getBuffer(FileID id) {
    if (!id)
        return nullptr;

    ASSERT(id.id < bufferEntries.size());
    return bufferEntries[id.id].buffer;
}

SourceBuffer* SourceManager::assignText(StringRef text) {
    return assignText("<unnamed_buffer" + std::to_string(unnamedBufferCount++) + ">", text);
}

SourceBuffer* SourceManager::assignText(StringRef path, StringRef text) {
    Buffer<char> buffer;
    buffer.appendRange(text);
    if (buffer.empty() || buffer.last() != '\0')
        buffer.append('\0');

    return assignBuffer(path, std::move(buffer));
}

SourceBuffer* SourceManager::assignBuffer(StringRef path, Buffer<char>&& buffer) {
    auto fullPath = fs::canonical(path.toString());
    auto canonicalStr = fullPath.string();
    auto it = lookupCache.find(canonicalStr);
    ASSERT(it == lookupCache.end());

    return cacheBuffer(std::move(canonicalStr), fullPath, std::move(buffer));
}

SourceBuffer* SourceManager::readSource(StringRef path) {
    // ensure that we have an absolute path
    ASSERT(path);
    path_type absPath = fs::absolute(path_type(path.begin(), path.end()), workingDir);
    return openCached(absPath);
}

SourceBuffer* SourceManager::readHeader(StringRef path, FileID includedFrom, bool isSystemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(path);
    path_type p(path.begin(), path.end());
    if (p.is_absolute())
        return openCached(p);

    // system path lookups only look in system directories
    if (isSystemPath) {
        for (auto& d : systemDirectories) {
            SourceBuffer* result = openCached(d / p);
            if (result)
                return result;
        }
        return nullptr;
    }

    // search relative to the current file
    const path_type* dir = bufferEntries[includedFrom.getValue()].directory;
    if (dir) {
        SourceBuffer* result = openCached((*dir) / p);
        if (result)
            return result;
    }

    // search additional include directories
    for (auto& d : userDirectories) {
        SourceBuffer* result = openCached(d / p);
        if (result)
            return result;
    }

    return nullptr;
}

SourceBuffer* SourceManager::openCached(path_type fullPath) {
    // first see if we have this cached
    fullPath = fs::canonical(fullPath);
    auto canonicalStr = fullPath.string();
    auto it = lookupCache.find(canonicalStr);
    if (it != lookupCache.end())
        return it->second.get();

    // do the read
    Buffer<char> buffer(0);
    if (!readFile(fullPath, buffer)) {
        lookupCache.emplace(std::move(canonicalStr), nullptr);
        return nullptr;
    }

    return cacheBuffer(std::move(canonicalStr), fullPath, std::move(buffer));
}

SourceBuffer* SourceManager::cacheBuffer(std::string&& canonicalPath, path_type& path, Buffer<char>&& buffer) {
    auto id = FileID::get(nextFileID++);
    auto result = lookupCache.emplace(std::move(canonicalPath), std::make_unique<SourceBuffer>(id, std::move(buffer))).first->second.get();

    BufferEntry entry;
    entry.buffer = result;
    entry.name = path.filename().string();
    entry.directory = &*directories.insert(path.remove_filename()).first;
    bufferEntries.push_back(std::move(entry));

    return result;
}

bool SourceManager::readFile(const path_type& path, Buffer<char>& buffer) {
    std::error_code ec;
    uintmax_t size = fs::file_size(path, ec);
    if (ec || size > INT32_MAX)
        return false;

    // null-terminate the buffer while we're at it
    buffer.extend((uint32_t)size + 1);
    std::ifstream stream(path, std::ios::binary);
    stream.read(buffer.begin(), size);

    buffer.begin()[(uint32_t)size] = '\0';

    return stream.good();
}

void SourceManager::computeLineOffsets(const Buffer<char>& buffer, std::vector<uint32_t>& offsets) {
    // first line always starts at offset 0
    offsets.push_back(0);

    const char* ptr = buffer.begin();
    const char* end = buffer.end();
    while (ptr != end) {
        if (ptr[0] == '\n' || ptr[0] == '\r') {
            // if we see \r\n or \n\r skip both chars
            if ((ptr[1] == '\n' || ptr[1] == '\r') && ptr[0] != ptr[1])
                ptr++;
            ptr++;
            offsets.push_back((uint32_t)(ptr - buffer.begin()));
        }
        else {
            ptr++;
        }
    }
}

}