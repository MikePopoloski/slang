//------------------------------------------------------------------------------
// SourceManager.cpp
// Source file management.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SourceManager.h"

#include "util/HashMap.h"

namespace slang {

SourceManager::SourceManager() {
    // add a dummy entry to the start of the directory list so that our file IDs line up
    FileInfo file;
    bufferEntries.emplace_back(file);
}

std::string SourceManager::makeAbsolutePath(string_view path) const {
    if (path.empty())
        return "";

    return Path::makeAbsolute(path).str();
}

void SourceManager::addSystemDirectory(string_view path) {
    systemDirectories.push_back(Path::makeAbsolute(path));
}

void SourceManager::addUserDirectory(string_view path) {
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

string_view SourceManager::getFileName(SourceLocation location) const {
    SourceLocation fileLocation = getFullyExpandedLoc(location);

    // Avoid computing line offsets if we just need a name of `line-less file
    FileData* fd = getFileData(fileLocation.buffer());
    if (!fd)
        return "";
    else if (fd->lineDirectives.empty())
        return string_view(fd->name);

    auto lineDirective = fd->getPreviousLineDirective(getRawLineNumber(fileLocation));
    if (!lineDirective)
        return string_view(fd->name);
    else
        return string_view(lineDirective->name);
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
    return std::get<ExpansionInfo>(bufferEntries[buffer.id]).originalLoc + (size_t)location.offset();
}

SourceLocation SourceManager::getFullyExpandedLoc(SourceLocation location) const {
    while (isMacroLoc(location))
        location = getExpansionLoc(location);
    return location;
}

string_view SourceManager::getSourceText(BufferID buffer) const {
    FileData* fd = getFileData(buffer);
    if (!fd)
        return "";

    return string_view(fd->mem.data(), fd->mem.size());
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc, SourceLocation expansionStart,
                                                 SourceLocation expansionEnd) {
    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionStart, expansionEnd));
    return SourceLocation(BufferID::get((uint32_t)(bufferEntries.size() - 1)), 0);
}

SourceBuffer SourceManager::assignText(string_view text, SourceLocation includedFrom) {
    // Generate a placeholder name for this "file"
    return assignText(string_view("<unnamed_buffer" + std::to_string(unnamedBufferCount++) + ">"), text, includedFrom);
}

SourceBuffer SourceManager::assignText(string_view path, string_view text, SourceLocation includedFrom) {
    std::vector<char> buffer;
    buffer.insert(buffer.end(), text.begin(), text.end());
    if (buffer.empty() || buffer.back() != '\0')
        buffer.push_back('\0');

    return assignBuffer(path, std::move(buffer), includedFrom);
}

SourceBuffer SourceManager::appendText(BufferID buffer, string_view text) {
    ASSERT(buffer);
    FileInfo& fi = std::get<FileInfo>(bufferEntries[buffer.id]);
    SourceLocation includeLoc = SourceLocation(buffer, (uint32_t)fi.data->mem.size());
    return assignText(text, includeLoc);
}

SourceBuffer SourceManager::assignBuffer(string_view path, std::vector<char>&& buffer, SourceLocation includedFrom) {
    Path fullPath = path;
    std::string canonicalStr = fullPath.str();
    auto it = lookupCache.find(canonicalStr);
    ASSERT(it == lookupCache.end());

    return cacheBuffer(std::move(canonicalStr), fullPath, includedFrom, std::move(buffer));
}

SourceBuffer SourceManager::readSource(string_view path) {
    ASSERT(!path.empty());
    return openCached(path, SourceLocation());
}

SourceBuffer SourceManager::readHeader(string_view path, SourceLocation includedFrom, bool isSystemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(!path.empty());
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
                                     string_view name, uint8_t level) {
    SourceLocation fileLocation = getFullyExpandedLoc(location);
    FileData* fd = getFileData(fileLocation.buffer());
    if (!fd)
        return;

    uint32_t sourceLineNum = getRawLineNumber(fileLocation);
    fd->lineDirectives.emplace_back(name, sourceLineNum, lineNum, level);
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
        string_view(fd->mem.data(), fd->mem.size()),
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
    std::vector<char> buffer;
    if (!absPath.readFile(buffer)) {
        lookupCache.emplace(std::move(canonicalStr), nullptr);
        return SourceBuffer();
    }

    return cacheBuffer(std::move(canonicalStr), absPath, includedFrom, std::move(buffer));
}

SourceBuffer SourceManager::cacheBuffer(std::string&& canonicalPath, const Path& path, SourceLocation includedFrom, std::vector<char>&& buffer) {
    std::string name = path.filename();
    auto fd = std::make_unique<FileData>(
        &*directories.insert(path.parentPath()).first,
        std::move(name),
        std::move(buffer)
    );

    FileData* fdPtr = lookupCache.emplace(std::move(canonicalPath), std::move(fd)).first->second.get();
    return createBufferEntry(fdPtr, includedFrom);
}

void SourceManager::computeLineOffsets(const std::vector<char>& buffer, std::vector<uint32_t>& offsets) {
    // first line always starts at offset 0
    offsets.push_back(0);

    const char* ptr = buffer.data();
    const char* end = buffer.data() + buffer.size();
    while (ptr != end) {
        if (ptr[0] == '\n' || ptr[0] == '\r') {
            // if we see \r\n or \n\r skip both chars
            if ((ptr[1] == '\n' || ptr[1] == '\r') && ptr[0] != ptr[1])
                ptr++;
            ptr++;
            offsets.push_back((uint32_t)(ptr - buffer.data()));
        }
        else {
            ptr++;
        }
    }
}

const SourceManager::LineDirectiveInfo*
SourceManager::FileData::getPreviousLineDirective(uint32_t rawLineNumber) const {
    auto it = std::lower_bound(lineDirectives.begin(), lineDirectives.end(),
                               LineDirectiveInfo("", rawLineNumber, 0, 0),
                               [](const auto& a, const auto& b) {
                                    return a.lineInFile < b.lineInFile;
                               });

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

    return nullptr;
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
    // So if it is equal, add one to the lower bound we got.
    uint32_t line = uint32_t(it - fd->lineOffsets.begin());
    if (it != fd->lineOffsets.end() && *it == location.offset())
        line++;
    return line;
}

}
