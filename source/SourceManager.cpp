#include "SourceManager.h"

#include <fstream>

namespace fs = std::tr2::sys;

namespace slang {

SourceManager::SourceManager() {
    workingDir = fs::current_path();

    // add a dummy entry to the start of the directory list so that our file IDs line up
    FileInfo file;
    bufferEntries.emplace_back(file);
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
    FileData* fd = getFileData(location.buffer);
    ASSERT(fd);

    // compute line offsets if we haven't already
    if (fd->lineOffsets.empty())
        computeLineOffsets(fd->mem, fd->lineOffsets);

    auto it = std::lower_bound(fd->lineOffsets.begin(), fd->lineOffsets.end(), location.offset);
    return (uint32_t)(it - fd->lineOffsets.begin());
}

uint32_t SourceManager::getColumnNumber(SourceLocation location) {
    FileData* fd = getFileData(location.buffer);
    ASSERT(fd);

    // walk backward to find start of line
    uint32_t lineStart = location.offset;
    ASSERT(lineStart < fd->mem.count());
    while (lineStart > 0 && fd->mem[lineStart - 1] != '\n' && fd->mem[lineStart - 1] != '\r')
        lineStart--;

    return location.offset - lineStart + 1;
}

StringRef SourceManager::getBufferName(BufferID buffer) {
    FileData* fd = getFileData(buffer);
    ASSERT(fd);

    return fd->name;
}

const Buffer<char>& SourceManager::getBufferMemory(BufferID buffer) {
    FileData* fd = getFileData(buffer);
    ASSERT(fd);

    return fd->mem;
}

SourceBuffer SourceManager::assignText(StringRef text) {
    return assignText("<unnamed_buffer" + std::to_string(unnamedBufferCount++) + ">", text);
}

SourceBuffer SourceManager::assignText(StringRef path, StringRef text) {
    Buffer<char> buffer;
    buffer.appendRange(text);
    if (buffer.empty() || buffer.back() != '\0')
        buffer.append('\0');

    return assignBuffer(path, std::move(buffer));
}

SourceBuffer SourceManager::assignBuffer(StringRef path, Buffer<char>&& buffer) {
    auto fullPath = fs::canonical(path.toString());
    auto canonicalStr = fullPath.string();
    auto it = lookupCache.find(canonicalStr);
    ASSERT(it == lookupCache.end());

    return cacheBuffer(std::move(canonicalStr), fullPath, std::move(buffer));
}

SourceBuffer SourceManager::readSource(StringRef path) {
    // ensure that we have an absolute path
    ASSERT(path);
    path_type absPath = fs::absolute(path_type(path.begin(), path.end()), workingDir);
    return openCached(absPath, SourceLocation());
}

SourceBuffer SourceManager::readHeader(StringRef path, SourceLocation includedFrom, bool isSystemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(path);
    path_type p(path.begin(), path.end());
    if (p.is_absolute())
        return openCached(p, includedFrom);

    // system path lookups only look in system directories
    if (isSystemPath) {
        for (auto& d : systemDirectories) {
            SourceBuffer result = openCached(d / p, includedFrom);
            if (result.id)
                return result;
        }
        return SourceBuffer();
    }

    // search relative to the current file
    FileData* fd = getFileData(includedFrom.buffer);
    if (fd && fd->directory) {
        SourceBuffer result = openCached((*fd->directory) / p, includedFrom);
        if (result.id)
            return result;
    }

    // search additional include directories
    for (auto& d : userDirectories) {
        SourceBuffer result = openCached(d / p, includedFrom);
        if (result.id)
            return result;
    }

    return SourceBuffer();
}

SourceManager::FileData* SourceManager::getFileData(BufferID buffer) {
    if (!buffer)
        return nullptr;

    ASSERT(buffer.id < bufferEntries.size());
    BufferEntry& entry = bufferEntries[buffer.id];

    ASSERT(entry.isFile);
    return entry.file.data;
}

SourceBuffer SourceManager::createBufferEntry(FileData* fd, SourceLocation includedFrom) {
    ASSERT(fd);
    bufferEntries.emplace_back(FileInfo(fd, includedFrom));
    return SourceBuffer { StringRef(fd->mem), BufferID::get(nextBufferID++) };
}

SourceBuffer SourceManager::openCached(path_type fullPath, SourceLocation includedFrom) {
    // first see if we have this file cached
    fullPath = fs::canonical(fullPath);
    auto canonicalStr = fullPath.string();
    auto it = lookupCache.find(canonicalStr);
    if (it != lookupCache.end()) {
        FileData* fd = it->second.get();
        return createBufferEntry(fd, includedFrom);
    }

    // do the read
    Buffer<char> buffer(0);
    if (!readFile(fullPath, buffer)) {
        lookupCache.emplace(std::move(canonicalStr), nullptr);
        return SourceBuffer();
    }

    return cacheBuffer(std::move(canonicalStr), fullPath, std::move(buffer));
}

SourceBuffer SourceManager::cacheBuffer(std::string&& canonicalPath, path_type& path, Buffer<char>&& buffer) {
    auto fd = std::make_unique<FileData>(
        &*directories.insert(path.remove_filename()).first,
        path.filename().string(),
        std::move(buffer)
    );

    FileData* fdPtr = lookupCache.emplace(std::move(canonicalPath), std::move(fd)).first->second.get();
    return createBufferEntry(fdPtr, SourceLocation());
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