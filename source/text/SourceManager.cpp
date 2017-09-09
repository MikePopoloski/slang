//------------------------------------------------------------------------------
// SourceManager.cpp
// Source file management.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SourceManager.h"

#include <algorithm>
#include <fstream>

#include "util/HashMap.h"

namespace slang {

SourceManager::SourceManager() {
    // add a dummy entry to the start of the directory list so that our file IDs line up
    FileInfo file;
    bufferEntries.emplace_back(file);
}

std::string SourceManager::makeAbsolutePath(StringRef path) const {
    if (!path)
        return "";

    return Path::makeAbsolute(path).str();
}

void SourceManager::addSystemDirectory(StringRef path) {
    systemDirectories.push_back(Path::makeAbsolute(path));
}

void SourceManager::addUserDirectory(StringRef path) {
    userDirectories.push_back(Path::makeAbsolute(path));
}

uint32_t SourceManager::getLineNumber(SourceLocation location) const {
    SourceLocation fileLocation = getFullyExpandedLoc(location);
    uint32_t rawLineNumber = getRawLineNumber(fileLocation);
    if (rawLineNumber == 0)
        return 0;

    FileData* fd = getFileData(fileLocation.buffer());
    auto lineDirective = fd->getPreviousLineDirective(rawLineNumber);

    if (!lineDirective)
        return rawLineNumber;
    else
        return lineDirective->lineOfDirective + (rawLineNumber - lineDirective->lineInFile) - 1;
}

uint32_t SourceManager::getColumnNumber(SourceLocation location) const {
    FileData* fd = getFileData(location.buffer());
    if (!fd)
        return 0;

    // walk backward to find start of line
    uint32_t lineStart = location.offset();
    ASSERT(lineStart < fd->mem.size());
    while (lineStart > 0 && fd->mem[lineStart - 1] != '\n' && fd->mem[lineStart - 1] != '\r')
        lineStart--;

    return location.offset() - lineStart + 1;
}

StringRef SourceManager::getFileName(SourceLocation location) const {
    SourceLocation fileLocation = getFullyExpandedLoc(location);

    // Avoid computing line offsets if we just need a name of `line-less file
    FileData* fd = getFileData(fileLocation.buffer());
    if (!fd)
        return nullptr;
    else if (fd->lineDirectives.empty())
        return StringRef(fd->name);

    auto lineDirective = fd->getPreviousLineDirective(getRawLineNumber(fileLocation));
    if (!lineDirective)
        return StringRef(fd->name);
    else
        return StringRef(lineDirective->name);
}

SourceLocation SourceManager::getIncludedFrom(BufferID buffer) const {
    if (!buffer)
        return SourceLocation();

    ASSERT(buffer.id < bufferEntries.size());
    return std::get<FileInfo>(bufferEntries[buffer.id]).includedFrom;
}

bool SourceManager::isFileLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    ASSERT(buffer.id < bufferEntries.size());
    return std::get_if<FileInfo>(&bufferEntries[buffer.id]) != nullptr;
}

bool SourceManager::isMacroLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    ASSERT(buffer.id < bufferEntries.size());
    return std::get_if<ExpansionInfo>(&bufferEntries[buffer.id]) != nullptr;
}

bool SourceManager::isIncludedFileLoc(SourceLocation location) const {
    return getIncludedFrom(location.buffer()).valid();
}

bool SourceManager::isBeforeInCompilationUnit(SourceLocation left, SourceLocation right) const {
    // Simple check: if they're in the same buffer, just do an easy compare
    if (left.buffer() == right.buffer())
        return left.offset() < right.offset();

    // TODO: add a cache for this?

    auto moveUp = [this](SourceLocation& sl) {
        if (!isFileLoc(sl))
            sl = getExpansionLoc(sl);
        else {
            SourceLocation included = getIncludedFrom(sl.buffer());
            if (!included)
                return true;
            sl = included;
        }
        return false;
    };

    // Otherwise we have to build the full include / expansion chain and compare.
    SmallHashMap<BufferID, uint32_t, 16> leftChain;
    do {
        leftChain.emplace(left.buffer(), left.offset());
    }
    while (left.buffer() != right.buffer() && !moveUp(left));

    SmallHashMap<BufferID, uint32_t, 16>::iterator it;
    while ((it = leftChain.find(right.buffer())) == leftChain.end()) {
        if (moveUp(right))
            break;
    }

    if (it != leftChain.end())
        left = SourceLocation(it->first, it->second);

    // At this point, we either have a nearest common ancestor, or the two
    // locations are simply in totally different compilation units.
    ASSERT(left.buffer() == right.buffer());
    return left.offset() < right.offset();
}

SourceLocation SourceManager::getExpansionLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceLocation();

    ASSERT(buffer.id < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.id]).expansionStart;
}

SourceRange SourceManager::getExpansionRange(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceRange();

    ASSERT(buffer.id < bufferEntries.size());
    const ExpansionInfo& info = std::get<ExpansionInfo>(bufferEntries[buffer.id]);
    return SourceRange(info.expansionStart, info.expansionEnd);
}

SourceLocation SourceManager::getOriginalLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceLocation();

    ASSERT(buffer.id < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.id]).originalLoc + location.offset();
}

SourceLocation SourceManager::getFullyExpandedLoc(SourceLocation location) const {
    while (isMacroLoc(location))
        location = getExpansionLoc(location);
    return location;
}

StringRef SourceManager::getSourceText(BufferID buffer) const {
    FileData* fd = getFileData(buffer);
    if (!fd)
        return nullptr;

    return StringRef(fd->mem);
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc, SourceLocation expansionStart,
                                                 SourceLocation expansionEnd) {
    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionStart, expansionEnd));
    return SourceLocation(BufferID::get((uint32_t)(bufferEntries.size() - 1)), 0);
}

SourceBuffer SourceManager::assignText(StringRef text, SourceLocation includedFrom) {
    // Generate a placeholder name for this "file"
    return assignText(StringRef("<unnamed_buffer" + std::to_string(unnamedBufferCount++) + ">"), text, includedFrom);
}

SourceBuffer SourceManager::assignText(StringRef path, StringRef text, SourceLocation includedFrom) {
    SmallVectorSized<char, 2> buffer;
    buffer.appendRange(text);
    if (buffer.empty() || buffer.back() != '\0')
        buffer.append('\0');

    return assignBuffer(path, std::move(buffer), includedFrom);
}

SourceBuffer SourceManager::appendText(BufferID buffer, StringRef text) {
    ASSERT(buffer);
    FileInfo& fi = std::get<FileInfo>(bufferEntries[buffer.id]);
    SourceLocation includeLoc = SourceLocation(buffer, fi.data->mem.size());
    return assignText(text, includeLoc);
}

SourceBuffer SourceManager::assignBuffer(StringRef path, Vector<char>&& buffer, SourceLocation includedFrom) {
    Path fullPath = path;
    std::string canonicalStr = fullPath.str();
    auto it = lookupCache.find(canonicalStr);
    ASSERT(it == lookupCache.end());

    return cacheBuffer(std::move(canonicalStr), fullPath, includedFrom, std::move(buffer));
}

SourceBuffer SourceManager::readSource(StringRef path) {
    ASSERT(path);
    return openCached(path, SourceLocation());
}

SourceBuffer SourceManager::readHeader(StringRef path, SourceLocation includedFrom, bool isSystemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(path);
    Path p = path;
    if (p.isAbsolute())
        return openCached(p, includedFrom);

    // system path lookups only look in system directories
    if (isSystemPath) {
        for (auto& d : systemDirectories) {
            SourceBuffer result = openCached(d + p, includedFrom);
            if (result.id)
                return result;
        }
        return SourceBuffer();
    }

    // search relative to the current file
    FileData* fd = getFileData(includedFrom.buffer());
    if (fd && fd->directory) {
        SourceBuffer result = openCached((*fd->directory) + p, includedFrom);
        if (result.id)
            return result;
    }

    // search additional include directories
    for (auto& d : userDirectories) {
        SourceBuffer result = openCached(d + p, includedFrom);
        if (result.id)
            return result;
    }

    return SourceBuffer();
}

void SourceManager::addLineDirective(SourceLocation location, uint32_t lineNum,
                                     StringRef name, uint8_t level) {
    SourceLocation fileLocation = getFullyExpandedLoc(location);
    FileData* fd = getFileData(fileLocation.buffer());
    if (!fd)
        return;

    uint32_t sourceLineNum = getRawLineNumber(fileLocation);
    fd->lineDirectives.emplace_back(sourceLineNum, lineNum, name, level);
}

SourceManager::FileData* SourceManager::getFileData(BufferID buffer) const {
    if (!buffer)
        return nullptr;

    ASSERT(buffer.id < bufferEntries.size());
    return std::get<FileInfo>(bufferEntries[buffer.id]).data;
}

SourceBuffer SourceManager::createBufferEntry(FileData* fd, SourceLocation includedFrom) {
    ASSERT(fd);
    bufferEntries.emplace_back(FileInfo(fd, includedFrom));
    return SourceBuffer {
        StringRef(fd->mem),
        BufferID::get((uint32_t)(bufferEntries.size() - 1))
    };
}

SourceBuffer SourceManager::openCached(const Path& fullPath, SourceLocation includedFrom) {
    Path absPath;
    try {
        absPath = Path::makeAbsolute(fullPath);
    }
    catch (std::runtime_error&) {
        return SourceBuffer();
    }

    // first see if we have this file cached
    std::string canonicalStr = absPath.str();
    auto it = lookupCache.find(canonicalStr);
    if (it != lookupCache.end()) {
        FileData* fd = it->second.get();
        if (!fd)
            return SourceBuffer();
        return createBufferEntry(fd, includedFrom);
    }

    // do the read
    Vector<char> buffer;
    if (!readFile(absPath, buffer)) {
        lookupCache.emplace(std::move(canonicalStr), nullptr);
        return SourceBuffer();
    }

    return cacheBuffer(std::move(canonicalStr), absPath, includedFrom, std::move(buffer));
}

SourceBuffer SourceManager::cacheBuffer(std::string&& canonicalPath, const Path& path, SourceLocation includedFrom, Vector<char>&& buffer) {
    std::string name = path.filename();
    auto fd = std::make_unique<FileData>(
        &*directories.insert(path.parentPath()).first,
        name,
        std::move(buffer)
    );

    FileData* fdPtr = lookupCache.emplace(std::move(canonicalPath), std::move(fd)).first->second.get();
    return createBufferEntry(fdPtr, includedFrom);
}

bool SourceManager::readFile(const Path& path, Vector<char>& buffer) {
    size_t size;
    try {
        size = path.fileSize();
    }
    catch (std::runtime_error&) {
        return false;
    }

    // + 1 for null terminator
    buffer.extend((uint32_t)size + 1);
    std::ifstream stream(path.str(), std::ios::binary);
    stream.read(buffer.begin(), size);

    // null-terminate the buffer while we're at it
    buffer.begin()[(uint32_t)size] = '\0';

    return stream.good();
}

void SourceManager::computeLineOffsets(const Vector<char>& buffer, std::vector<uint32_t>& offsets) {
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

const SourceManager::FileData::LineDirectiveInfo*
SourceManager::FileData::getPreviousLineDirective(uint32_t rawLineNumber) const {
    auto it = std::lower_bound(lineDirectives.begin(), lineDirectives.end(),
        LineDirectiveInfo(rawLineNumber, 0, "", 0), LineDirectiveComparator());

    if (it != lineDirectives.begin()) {
        // lower_bound will give us an iterator to the first directive after the command
        // let's instead get a pointer to the one right before it
        if (it == lineDirectives.end()) {
            // Check to see whether the actual last directive is before the
            // given line number
            if (lineDirectives.back().lineInFile >= rawLineNumber)
                return nullptr;
        }
        return &*(it - 1);
    }
    else {
        return nullptr;
    }
}

uint32_t SourceManager::getRawLineNumber(SourceLocation location) const {
    FileData* fd = getFileData(location.buffer());
    if (!fd)
        return 0;

    // compute line offsets if we haven't already
    if (fd->lineOffsets.empty())
        computeLineOffsets(fd->mem, fd->lineOffsets);

    // Find the first line offset that is greater than the given location offset. That iterator
    // then tells us how many lines away from the beginning we are.
    auto it = std::lower_bound(fd->lineOffsets.begin(), fd->lineOffsets.end(), location.offset());

    // We want to ensure the line we return is strictly greater than the given location offset.
    // So if it is equal, add one to the lower bound we got
    uint32_t line = uint32_t(it - fd->lineOffsets.begin());
    if (it != fd->lineOffsets.end() && *it == location.offset())
        line++;
    return line;
}

}
