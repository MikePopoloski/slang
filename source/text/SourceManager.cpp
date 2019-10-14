//------------------------------------------------------------------------------
// SourceManager.cpp
// Source file management.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/text/SourceManager.h"

#include <fstream>
#include <string>

#include "slang/util/StackContainer.h"

namespace slang {

SourceManager::SourceManager() {
    // add a dummy entry to the start of the directory list so that our file IDs line up
    FileInfo file;
    bufferEntries.emplace_back(file);
}

std::string SourceManager::makeAbsolutePath(string_view path) const {
    return fs::canonical(path).string();
}

void SourceManager::addSystemDirectory(string_view path) {
    systemDirectories.push_back(fs::canonical(widen(path)));
}

void SourceManager::addUserDirectory(string_view path) {
    userDirectories.push_back(fs::canonical(widen(path)));
}

size_t SourceManager::getLineNumber(SourceLocation location) const {
    SourceLocation fileLocation = getFullyExpandedLoc(location);
    size_t rawLineNumber = getRawLineNumber(fileLocation);
    if (rawLineNumber == 0)
        return 0;

    FileData* fd = getFileData(fileLocation.buffer());
    auto lineDirective = fd->getPreviousLineDirective(rawLineNumber);

    if (!lineDirective)
        return rawLineNumber;
    else
        return lineDirective->lineOfDirective + (rawLineNumber - lineDirective->lineInFile) - 1;
}

size_t SourceManager::getColumnNumber(SourceLocation location) const {
    FileData* fd = getFileData(location.buffer());
    if (!fd)
        return 0;

    // walk backward to find start of line
    size_t lineStart = location.offset();
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

string_view SourceManager::getRawFileName(BufferID buffer) const {
    FileData* fd = getFileData(buffer);
    if (!fd)
        return "";
    else
        return string_view(fd->name);
}

SourceLocation SourceManager::getIncludedFrom(BufferID buffer) const {
    if (!buffer)
        return SourceLocation();

    ASSERT(buffer.getId() < bufferEntries.size());
    const FileInfo* info = std::get_if<FileInfo>(&bufferEntries[buffer.getId()]);
    return info ? info->includedFrom : SourceLocation();
}

string_view SourceManager::getMacroName(SourceLocation location) const {
    while (isMacroArgLoc(location))
        location = getExpansionLoc(location);

    auto buffer = location.buffer();
    if (!buffer)
        return {};

    ASSERT(buffer.getId() < bufferEntries.size());
    auto info = std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]);
    if (!info)
        return {};

    return info->macroName;
}

bool SourceManager::isFileLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    ASSERT(buffer.getId() < bufferEntries.size());
    return std::get_if<FileInfo>(&bufferEntries[buffer.getId()]) != nullptr;
}

bool SourceManager::isMacroLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    ASSERT(buffer.getId() < bufferEntries.size());
    return std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]) != nullptr;
}

bool SourceManager::isMacroArgLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    ASSERT(buffer.getId() < bufferEntries.size());
    auto info = std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]);
    return info && info->isMacroArg;
}

bool SourceManager::isIncludedFileLoc(SourceLocation location) const {
    return getIncludedFrom(location.buffer()).valid();
}

bool SourceManager::isPreprocessedLoc(SourceLocation location) const {
    return isMacroLoc(location) || isIncludedFileLoc(location);
}

bool SourceManager::isBeforeInCompilationUnit(SourceLocation left, SourceLocation right) const {
    // Simple check: if they're in the same buffer, just do an easy compare
    if (left.buffer() == right.buffer())
        return left.offset() < right.offset();

    auto moveUp = [this](SourceLocation& sl) {
        if (sl && !isFileLoc(sl))
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
    SmallMap<BufferID, size_t, 16> leftChain;
    do {
        leftChain.emplace(left.buffer(), left.offset());
    } while (left.buffer() != right.buffer() && !moveUp(left));

    SmallMap<BufferID, size_t, 16>::iterator it;
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

    ASSERT(buffer.getId() < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.getId()]).expansionRange.start();
}

SourceRange SourceManager::getExpansionRange(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceRange();

    ASSERT(buffer.getId() < bufferEntries.size());
    const ExpansionInfo& info = std::get<ExpansionInfo>(bufferEntries[buffer.getId()]);
    return info.expansionRange;
}

SourceLocation SourceManager::getOriginalLoc(SourceLocation location) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceLocation();

    ASSERT(buffer.getId() < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.getId()]).originalLoc + location.offset();
}

SourceLocation SourceManager::getFullyOriginalLoc(SourceLocation location) const {
    while (isMacroLoc(location))
        location = getOriginalLoc(location);
    return location;
}

SourceLocation SourceManager::getFullyExpandedLoc(SourceLocation location) const {
    while (isMacroLoc(location)) {
        if (isMacroArgLoc(location))
            location = getOriginalLoc(location);
        else
            location = getExpansionLoc(location);
    }
    return location;
}

string_view SourceManager::getSourceText(BufferID buffer) const {
    FileData* fd = getFileData(buffer);
    if (!fd)
        return "";

    return string_view(fd->mem.data(), fd->mem.size());
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc,
                                                 SourceRange expansionRange, bool isMacroArg) {
    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionRange, isMacroArg));
    return SourceLocation(BufferID((uint32_t)(bufferEntries.size() - 1), ""sv), 0);
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc,
                                                 SourceRange expansionRange,
                                                 string_view macroName) {
    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionRange, macroName));
    return SourceLocation(BufferID((uint32_t)(bufferEntries.size() - 1), macroName), 0);
}

SourceBuffer SourceManager::assignText(string_view text, SourceLocation includedFrom) {
    return assignText("", text, includedFrom);
}

SourceBuffer SourceManager::assignText(string_view path, string_view text,
                                       SourceLocation includedFrom) {
    std::string temp;
    if (path.empty()) {
        using namespace std::literals;
        temp = "<unnamed_buffer"s + std::to_string(unnamedBufferCount++) + ">"s;
        path = temp;
    }

    std::vector<char> buffer;
    buffer.insert(buffer.end(), text.begin(), text.end());
    if (buffer.empty() || buffer.back() != '\0')
        buffer.push_back('\0');

    return assignBuffer(path, std::move(buffer), includedFrom);
}

SourceBuffer SourceManager::assignBuffer(string_view path, std::vector<char>&& buffer,
                                         SourceLocation includedFrom) {
    userFileBuffers.emplace_back(FileData(nullptr, std::string(path), std::move(buffer)));

    FileData* fd = &userFileBuffers.back();
    userFileLookup[std::string(path)] = fd;
    return createBufferEntry(fd, includedFrom);
}

SourceBuffer SourceManager::readSource(string_view path) {
    ASSERT(!path.empty());
    return openCached(widen(path), SourceLocation());
}

SourceBuffer SourceManager::readHeader(string_view path, SourceLocation includedFrom,
                                       bool isSystemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(!path.empty());
    fs::path p = widen(path);
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
    FileData* fd = getFileData(includedFrom.buffer());
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

    // As a last resort, check for user specified in-memory buffers.
    if (auto it = userFileLookup.find(std::string(path)); it != userFileLookup.end()) {
        return createBufferEntry(it->second, includedFrom);
    }

    return SourceBuffer();
}

void SourceManager::addLineDirective(SourceLocation location, size_t lineNum, string_view name,
                                     uint8_t level) {
    SourceLocation fileLocation = getFullyExpandedLoc(location);
    FileData* fd = getFileData(fileLocation.buffer());
    if (!fd)
        return;

    fs::path full;
    fs::path linePath = widen(name);
    if (linePath.has_relative_path())
        full = linePath.lexically_proximate(fs::current_path());
    else
        full = fs::path(widen(fd->name)).replace_filename(linePath);

    size_t sourceLineNum = getRawLineNumber(fileLocation);
    fd->lineDirectives.emplace_back(full.u8string(), sourceLineNum, lineNum, level);
}

SourceManager::FileData* SourceManager::getFileData(BufferID buffer) const {
    if (!buffer)
        return nullptr;

    ASSERT(buffer.getId() < bufferEntries.size());
    return std::get<FileInfo>(bufferEntries[buffer.getId()]).data;
}

SourceBuffer SourceManager::createBufferEntry(FileData* fd, SourceLocation includedFrom) {
    ASSERT(fd);
    bufferEntries.emplace_back(FileInfo(fd, includedFrom));
    return SourceBuffer{ string_view(fd->mem.data(), fd->mem.size()),
                         BufferID((uint32_t)(bufferEntries.size() - 1), fd->name) };
}

SourceBuffer SourceManager::openCached(const fs::path& fullPath, SourceLocation includedFrom) {
    std::error_code ec;
    fs::path absPath = fs::canonical(fullPath, ec);
    if (ec)
        return SourceBuffer();

    // first see if we have this file cached
    auto it = lookupCache.find(absPath.u8string());
    if (it != lookupCache.end()) {
        FileData* fd = it->second.get();
        if (!fd)
            return SourceBuffer();
        return createBufferEntry(fd, includedFrom);
    }

    // do the read
    std::vector<char> buffer;
    if (!readFile(absPath, buffer)) {
        lookupCache.emplace(absPath.u8string(), nullptr);
        return SourceBuffer();
    }

    return cacheBuffer(absPath, includedFrom, std::move(buffer));
}

SourceBuffer SourceManager::cacheBuffer(const fs::path& path, SourceLocation includedFrom,
                                        std::vector<char>&& buffer) {
    std::string name;
    std::error_code ec;
    fs::path rel = fs::proximate(path, ec);
    if (ec || rel.empty())
        name = path.filename().u8string();
    else
        name = rel.u8string();

    auto fd = std::make_unique<FileData>(&*directories.insert(path.parent_path()).first,
                                         std::move(name), std::move(buffer));

    FileData* fdPtr = lookupCache.emplace(path.u8string(), std::move(fd)).first->second.get();
    return createBufferEntry(fdPtr, includedFrom);
}

void SourceManager::computeLineOffsets(const std::vector<char>& buffer,
                                       std::vector<size_t>& offsets) {
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
            offsets.push_back((size_t)(ptr - buffer.data()));
        }
        else {
            ptr++;
        }
    }
}

bool SourceManager::readFile(const fs::path& path, std::vector<char>& buffer) {
    std::error_code ec;
    uintmax_t size = fs::file_size(path, ec);
    if (ec)
        return false;

    // + 1 for null terminator
    buffer.resize((size_t)size + 1);
    std::ifstream stream(path, std::ios::binary);
    if (!stream.read(buffer.data(), (std::streamsize)size))
        return false;

    // null-terminate the buffer while we're at it
    size_t sz = (size_t)stream.gcount();
    buffer.resize(sz + 1);
    buffer[sz] = '\0';

    return true;
}

const SourceManager::LineDirectiveInfo* SourceManager::FileData::getPreviousLineDirective(
    size_t rawLineNumber) const {
    auto it = std::lower_bound(
        lineDirectives.begin(), lineDirectives.end(), LineDirectiveInfo("", rawLineNumber, 0, 0),
        [](const auto& a, const auto& b) { return a.lineInFile < b.lineInFile; });

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

size_t SourceManager::getRawLineNumber(SourceLocation location) const {
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
    size_t line = size_t(it - fd->lineOffsets.begin());
    if (it != fd->lineOffsets.end() && *it == location.offset())
        line++;
    return line;
}

} // namespace slang
