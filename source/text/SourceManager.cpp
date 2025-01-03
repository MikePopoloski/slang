//------------------------------------------------------------------------------
// SourceManager.cpp
// Source file management
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/text/SourceManager.h"

#include <string>

#include "slang/text/Glob.h"
#include "slang/util/OS.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang {

static const fs::path emptyPath;

SourceManager::SourceManager() {
    // add a dummy entry to the start of the directory list so that our file IDs line up
    FileInfo file;
    bufferEntries.emplace_back(file);
}

std::error_code SourceManager::addSystemDirectories(std::string_view pattern) {
    SmallVector<fs::path> dirs;
    std::error_code ec;
    svGlob({}, pattern, GlobMode::Directories, dirs, /* expandEnvVars */ false, ec);

    // Note: locking the separate mutex for include dirs here.
    std::unique_lock lock(includeDirMutex);
    systemDirectories.insert(systemDirectories.end(), dirs.begin(), dirs.end());
    return ec;
}

std::error_code SourceManager::addUserDirectories(std::string_view pattern) {
    SmallVector<fs::path> dirs;
    std::error_code ec;
    svGlob({}, pattern, GlobMode::Directories, dirs, /* expandEnvVars */ false, ec);

    // Note: locking the separate mutex for include dirs here.
    std::unique_lock lock(includeDirMutex);
    userDirectories.insert(userDirectories.end(), dirs.begin(), dirs.end());
    return ec;
}

size_t SourceManager::getLineNumber(SourceLocation location) const {
    std::shared_lock lock(mutex);
    SourceLocation fileLocation = getFullyExpandedLocImpl(location, lock);
    size_t rawLineNumber = getRawLineNumber(fileLocation, lock);
    if (rawLineNumber == 0)
        return 0;

    auto info = getFileInfo(fileLocation.buffer(), lock);

    auto lineDirective = info->getPreviousLineDirective(rawLineNumber);
    if (!lineDirective)
        return rawLineNumber;
    else
        return lineDirective->lineOfDirective + (rawLineNumber - lineDirective->lineInFile) - 1;
}

size_t SourceManager::getColumnNumber(SourceLocation location) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(location.buffer(), lock);
    if (!info || !info->data)
        return 0;

    // walk backward to find start of line
    auto fd = info->data;
    size_t lineStart = location.offset();
    SLANG_ASSERT(lineStart < fd->mem.size());
    while (lineStart > 0 && fd->mem[lineStart - 1] != '\n' && fd->mem[lineStart - 1] != '\r')
        lineStart--;

    return location.offset() - lineStart + 1;
}

std::string_view SourceManager::getFileName(SourceLocation location) const {
    std::shared_lock lock(mutex);
    SourceLocation fileLocation = getFullyExpandedLocImpl(location, lock);
    auto info = getFileInfo(fileLocation.buffer(), lock);
    if (!info || !info->data)
        return "";

    // Avoid computing line offsets if we just need a name of `line-less file
    if (info->lineDirectives.empty())
        return info->data->name;

    size_t rawLine = getRawLineNumber(fileLocation, lock);
    auto lineDirective = info->getPreviousLineDirective(rawLine);
    if (!lineDirective)
        return info->data->name;
    else
        return lineDirective->name;
}

std::string_view SourceManager::getRawFileName(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info || !info->data)
        return "";

    return info->data->name;
}

const fs::path& SourceManager::getFullPath(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info || !info->data)
        return emptyPath;

    return info->data->fullPath;
}

SourceLocation SourceManager::getIncludedFrom(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info)
        return SourceLocation();

    return info->includedFrom;
}

const SourceLibrary* SourceManager::getLibraryFor(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info)
        return nullptr;

    return info->library;
}

std::string_view SourceManager::getMacroName(SourceLocation location) const {
    std::shared_lock lock(mutex);
    while (isMacroArgLocImpl(location, lock))
        location = getExpansionRangeImpl(location, lock).start();

    auto buffer = location.buffer();
    if (!buffer)
        return {};

    SLANG_ASSERT(buffer.getId() < bufferEntries.size());
    auto info = std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]);
    if (!info)
        return {};

    return info->macroName;
}

bool SourceManager::isFileLoc(SourceLocation location) const {
    if (location.buffer() == SourceLocation::NoLocation.buffer())
        return false;

    std::shared_lock lock(mutex);
    return getFileInfo(location.buffer(), lock) != nullptr;
}

bool SourceManager::isMacroLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return isMacroLocImpl(location, lock);
}

bool SourceManager::isMacroArgLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return isMacroArgLocImpl(location, lock);
}

bool SourceManager::isIncludedFileLoc(SourceLocation location) const {
    return getIncludedFrom(location.buffer()).valid();
}

bool SourceManager::isPreprocessedLoc(SourceLocation location) const {
    return isMacroLoc(location) || isIncludedFileLoc(location);
}

std::optional<bool> SourceManager::isBeforeInCompilationUnit(SourceLocation left,
                                                             SourceLocation right) const {
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
    if (left.buffer() == right.buffer())
        return left.offset() < right.offset();

    return std::nullopt;
}

SourceLocation SourceManager::getExpansionLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return getExpansionRangeImpl(location, lock).start();
}

SourceRange SourceManager::getExpansionRange(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return getExpansionRangeImpl(location, lock);
}

SourceLocation SourceManager::getOriginalLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return getOriginalLocImpl(location, lock);
}

SourceLocation SourceManager::getFullyOriginalLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    while (isMacroLocImpl(location, lock))
        location = getOriginalLocImpl(location, lock);
    return location;
}

SourceRange SourceManager::getFullyOriginalRange(SourceRange range) const {
    SourceLocation start(getFullyOriginalLoc(range.start()));
    SourceLocation end(getFullyOriginalLoc(range.end()));
    return SourceRange(start, end);
}

SourceLocation SourceManager::getFullyExpandedLoc(SourceLocation location) const {
    std::shared_lock lock(mutex);
    return getFullyExpandedLocImpl(location, lock);
}

std::string_view SourceManager::getSourceText(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info || !info->data)
        return "";

    auto fd = info->data;
    return std::string_view(fd->mem.data(), fd->mem.size());
}

uint64_t SourceManager::getSortKey(BufferID buffer) const {
    std::shared_lock lock(mutex);
    auto info = getFileInfo(buffer, lock);
    if (!info)
        return uint64_t(buffer.getId()) << 32;

    return info->sortKey;
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc,
                                                 SourceRange expansionRange, bool isMacroArg) {
    std::unique_lock lock(mutex);

    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionRange, isMacroArg));
    return SourceLocation(BufferID((uint32_t)(bufferEntries.size() - 1), ""sv), 0);
}

SourceLocation SourceManager::createExpansionLoc(SourceLocation originalLoc,
                                                 SourceRange expansionRange,
                                                 std::string_view macroName) {
    std::unique_lock lock(mutex);

    bufferEntries.emplace_back(ExpansionInfo(originalLoc, expansionRange, macroName));
    return SourceLocation(BufferID((uint32_t)(bufferEntries.size() - 1), macroName), 0);
}

SourceBuffer SourceManager::assignText(std::string_view text, SourceLocation includedFrom,
                                       const SourceLibrary* library) {
    return assignText("", text, includedFrom, library);
}

SourceBuffer SourceManager::assignText(std::string_view path, std::string_view text,
                                       SourceLocation includedFrom, const SourceLibrary* library) {
    std::string temp;
    if (path.empty()) {
        using namespace std::literals;
        temp = "<unnamed_buffer"s + std::to_string(unnamedBufferCount++) + ">"s;
        path = temp;
    }

    SmallVector<char> buffer;
    buffer.insert(buffer.end(), text.begin(), text.end());
    if (buffer.empty() || buffer.back() != '\0')
        buffer.push_back('\0');

    return assignBuffer(path, std::move(buffer), includedFrom, library);
}

SourceBuffer SourceManager::assignBuffer(std::string_view bufferPath, SmallVector<char>&& buffer,
                                         SourceLocation includedFrom,
                                         const SourceLibrary* library) {
    // first see if we have this file cached
    fs::path path(bufferPath);
    auto pathStr = getU8Str(path);
    {
        std::shared_lock lock(mutex);
        auto it = lookupCache.find(pathStr);
        if (it != lookupCache.end()) {
            SLANG_THROW(std::runtime_error(
                "Buffer with the given path has already been assigned to the source manager"));
        }
    }

    return cacheBuffer(std::move(path), std::move(pathStr), includedFrom, library, UINT64_MAX,
                       std::move(buffer));
}

SourceManager::BufferOrError SourceManager::readSource(const fs::path& path,
                                                       const SourceLibrary* library,
                                                       uint64_t sortKey) {
    return openCached(path, SourceLocation(), library, sortKey);
}

SourceManager::BufferOrError SourceManager::readHeader(
    std::string_view path, SourceLocation includedFrom, const SourceLibrary* library,
    bool isSystemPath, std::span<std::filesystem::path const> additionalIncludePaths) {

    // if the header is specified as an absolute path, just do a straight lookup
    SLANG_ASSERT(!path.empty());
    fs::path p = path;
    if (p.is_absolute())
        return openCached(p, includedFrom, library);

    // system path lookups only look in system directories
    if (isSystemPath) {
        // Separate lock for the include dirs here so that we can iterate
        // over them without having to make a copy. It's unlikely that the
        // list is being modified while we're reading headers anyway.
        std::shared_lock includeDirLock(includeDirMutex);
        for (auto& d : systemDirectories) {
            auto result = openCached(d / p, includedFrom, library);
            if (result)
                return result;
        }
        return nonstd::make_unexpected(make_error_code(std::errc::no_such_file_or_directory));
    }

    // search relative to the current file
    const fs::path* currFileDir = nullptr;
    {
        std::shared_lock lock(mutex);
        auto info = getFileInfo(includedFrom.buffer(), lock);
        if (info && info->data)
            currFileDir = info->data->directory;
    }

    if (currFileDir) {
        auto result = openCached(*currFileDir / p, includedFrom, library);
        if (result)
            return result;
    }

    for (auto& dir : additionalIncludePaths) {
        auto result = openCached(dir / p, includedFrom, library);
        if (result)
            return result;
    }

    // Use library-specific include dirs if they exist.
    if (library) {
        for (auto& dir : library->includeDirs) {
            auto result = openCached(dir / p, includedFrom, library);
            if (result)
                return result;
        }
    }

    // See comment above about this separate mutex / lock.
    std::shared_lock includeDirLock(includeDirMutex);
    for (auto& d : userDirectories) {
        auto result = openCached(d / p, includedFrom, library);
        if (result)
            return result;
    }

    return nonstd::make_unexpected(make_error_code(std::errc::no_such_file_or_directory));
}

void SourceManager::addLineDirective(SourceLocation location, size_t lineNum, std::string_view name,
                                     uint8_t level) {
    std::unique_lock lock(mutex);
    SourceLocation fileLocation = getFullyExpandedLocImpl(location, lock);
    FileInfo* info = getFileInfo(fileLocation.buffer(), lock);
    if (!info || !info->data)
        return;

    fs::path full;
    fs::path linePath = name;
    std::error_code ec;
    if (!disableProximatePaths && linePath.has_relative_path())
        full = linePath.lexically_proximate(fs::current_path(ec));
    else
        full = fs::path(info->data->name).replace_filename(linePath);

    size_t sourceLineNum = getRawLineNumber(fileLocation, lock);
    info->lineDirectives.emplace_back(std::string(getU8Str(full)), sourceLineNum, lineNum, level);
}

void SourceManager::addDiagnosticDirective(SourceLocation location, std::string_view name,
                                           DiagnosticSeverity severity) {
    std::unique_lock lock(mutex);
    SourceLocation fileLocation = getFullyExpandedLocImpl(location, lock);

    size_t offset = fileLocation.offset();
    auto& vec = diagDirectives[fileLocation.buffer()];
    if (vec.empty() || offset >= vec.back().offset)
        vec.emplace_back(name, offset, severity);
    else {
        // Keep the list in sorted order. Typically new additions should be at the end,
        // in which case we'll hit the condition above, but just in case we will do the
        // full search and insert here.
        vec.emplace(std::ranges::upper_bound(vec, offset, {}, &DiagnosticDirectiveInfo::offset),
                    name, offset, severity);
    }
}

std::span<const SourceManager::DiagnosticDirectiveInfo> SourceManager::getDiagnosticDirectives(
    BufferID buffer) const {
    if (auto it = diagDirectives.find(buffer); it != diagDirectives.end())
        return it->second;
    return {};
}

void SourceManager::clearDiagnosticDirectives() {
    std::unique_lock lock(mutex);
    diagDirectives.clear();
}

std::vector<BufferID> SourceManager::getAllBuffers() const {
    std::shared_lock lock(mutex);
    std::vector<BufferID> result;
    for (size_t i = 1; i < bufferEntries.size(); i++)
        result.push_back(BufferID((uint32_t)i, ""sv));

    return result;
}

template<IsLock TLock>
SourceManager::FileInfo* SourceManager::getFileInfo(BufferID buffer, TLock&) {
    if (!buffer || buffer.getId() >= bufferEntries.size())
        return nullptr;

    return std::get_if<FileInfo>(&bufferEntries[buffer.getId()]);
}

template<IsLock TLock>
const SourceManager::FileInfo* SourceManager::getFileInfo(BufferID buffer, TLock&) const {
    if (!buffer || buffer.getId() >= bufferEntries.size())
        return nullptr;

    return std::get_if<FileInfo>(&bufferEntries[buffer.getId()]);
}

SourceBuffer SourceManager::createBufferEntry(FileData* fd, SourceLocation includedFrom,
                                              const SourceLibrary* library, uint64_t sortKey,
                                              std::unique_lock<std::shared_mutex>&) {
    SLANG_ASSERT(fd);

    // If no sort key is provided we use the bufferID, but shifted up
    // so that the bottom 32 bits are reserved for custom sort keys.
    if (sortKey == UINT64_MAX)
        sortKey = bufferEntries.size() << 32;

    bufferEntries.emplace_back(FileInfo(fd, library, includedFrom, sortKey));
    return SourceBuffer{std::string_view(fd->mem.data(), fd->mem.size()), library,
                        BufferID((uint32_t)(bufferEntries.size() - 1), fd->name)};
}

bool SourceManager::isCached(const fs::path& path) const {
    fs::path absPath;
    if (!disableProximatePaths) {
        std::error_code ec;
        absPath = fs::weakly_canonical(path, ec);
        if (ec)
            return false;
    }
    else {
        absPath = path;
    }

    std::shared_lock lock(mutex);
    auto it = lookupCache.find(getU8Str(absPath));
    return it != lookupCache.end();
}

SourceManager::BufferOrError SourceManager::openCached(const fs::path& fullPath,
                                                       SourceLocation includedFrom,
                                                       const SourceLibrary* library,
                                                       uint64_t sortKey) {
    fs::path absPath;
    if (!disableProximatePaths) {
        std::error_code ec;
        absPath = fs::weakly_canonical(fullPath, ec);
        if (ec)
            return nonstd::make_unexpected(ec);
    }
    else {
        absPath = fullPath;
    }

    // first see if we have this file cached
    std::string pathStr = getU8Str(absPath);
    {
        std::unique_lock lock(mutex);
        auto it = lookupCache.find(pathStr);
        if (it != lookupCache.end()) {
            auto& [fd, ec] = it->second;
            if (ec)
                return nonstd::make_unexpected(ec);

            SLANG_ASSERT(fd);
            return createBufferEntry(fd.get(), includedFrom, library, sortKey, lock);
        }
    }

    // do the read
    SmallVector<char> buffer;
    if (std::error_code ec = OS::readFile(absPath, buffer)) {
        std::unique_lock lock(mutex);
        lookupCache.emplace(pathStr, std::pair{nullptr, ec});
        return nonstd::make_unexpected(ec);
    }

    return cacheBuffer(std::move(absPath), std::move(pathStr), includedFrom, library, sortKey,
                       std::move(buffer));
}

SourceBuffer SourceManager::cacheBuffer(fs::path&& path, std::string&& pathStr,
                                        SourceLocation includedFrom, const SourceLibrary* library,
                                        uint64_t sortKey, SmallVector<char>&& buffer) {
    std::string name;
    if (!disableProximatePaths) {
        std::error_code ec;
        name = getU8Str(fs::proximate(path, ec));
        if (ec)
            name = {};
    }

    if (name.empty())
        name = getU8Str(path.filename());

    std::unique_lock lock(mutex);

    auto directory = &*directories.insert(path.parent_path()).first;
    auto fd = std::make_unique<FileData>(directory, std::move(name), std::move(buffer),
                                         std::move(path));

    // Note: it's possible that insertion here fails due to another thread
    // racing against us to open and insert the same file. We do a lookup
    // in the cache before proceeding to read the file but we drop the lock
    // during the read. It's not actually a problem, we'll just use the data
    // we already loaded (just like we had gotten a hit on the cache in the
    // first place).
    auto [it, inserted] = lookupCache.emplace(pathStr, std::pair{std::move(fd), std::error_code{}});

    FileData* fdPtr = it->second.first.get();
    return createBufferEntry(fdPtr, includedFrom, library, sortKey, lock);
}

template<IsLock TLock>
size_t SourceManager::getRawLineNumber(SourceLocation location, TLock& readLock) const {
    FileData* fd;
    {
        // Separate scope so that info isn't used after it may potentially
        // get invalidated when we briefly unloack a read lock and grab a
        // write lock below.
        const FileInfo* info = getFileInfo(location.buffer(), readLock);
        if (!info || !info->data)
            return 0;

        fd = info->data;
    }

    if (fd->lineOffsets.empty()) {
        // We need to compute line offsets. If the lock is a write lock then
        // we can just go ahead and do that; if not we need to unlock the
        // read lock and grab a write lock.
        if constexpr (std::is_same_v<TLock, std::shared_lock<std::shared_mutex>>) {
            readLock.unlock();

            std::unique_lock writeLock(mutex);
            computeLineOffsets(fd->mem, fd->lineOffsets);

            writeLock.unlock();
            readLock.lock();
        }
        else {
            computeLineOffsets(fd->mem, fd->lineOffsets);
        }
    }

    // Find the first line offset that is greater than the given location offset. That iterator
    // then tells us how many lines away from the beginning we are.
    auto it = std::ranges::lower_bound(fd->lineOffsets, location.offset());

    // We want to ensure the line we return is strictly greater than the given location offset.
    // So if it is equal, add one to the lower bound we got.
    size_t line = size_t(it - fd->lineOffsets.begin());
    if (it != fd->lineOffsets.end() && *it == location.offset())
        line++;
    return line;
}

template<IsLock TLock>
SourceLocation SourceManager::getFullyExpandedLocImpl(SourceLocation location, TLock& lock) const {
    while (isMacroLocImpl(location, lock)) {
        if (isMacroArgLocImpl(location, lock))
            location = getOriginalLocImpl(location, lock);
        else
            location = getExpansionRangeImpl(location, lock).start();
    }
    return location;
}

template<IsLock TLock>
bool SourceManager::isMacroLocImpl(SourceLocation location, TLock&) const {
    if (location.buffer() == SourceLocation::NoLocation.buffer())
        return false;

    auto buffer = location.buffer();
    if (!buffer)
        return false;

    SLANG_ASSERT(buffer.getId() < bufferEntries.size());
    return std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]) != nullptr;
}

template<IsLock TLock>
bool SourceManager::isMacroArgLocImpl(SourceLocation location, TLock&) const {
    if (location == SourceLocation::NoLocation)
        return false;

    auto buffer = location.buffer();
    if (!buffer)
        return false;

    SLANG_ASSERT(buffer.getId() < bufferEntries.size());
    auto info = std::get_if<ExpansionInfo>(&bufferEntries[buffer.getId()]);
    return info && info->isMacroArg;
}

template<IsLock TLock>
SourceRange SourceManager::getExpansionRangeImpl(SourceLocation location, TLock&) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceRange();

    SLANG_ASSERT(buffer.getId() < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.getId()]).expansionRange;
}

template<IsLock TLock>
SourceLocation SourceManager::getOriginalLocImpl(SourceLocation location, TLock&) const {
    auto buffer = location.buffer();
    if (!buffer)
        return SourceLocation();

    SLANG_ASSERT(buffer.getId() < bufferEntries.size());
    return std::get<ExpansionInfo>(bufferEntries[buffer.getId()]).originalLoc + location.offset();
}

void SourceManager::computeLineOffsets(const SmallVector<char>& buffer,
                                       std::vector<size_t>& offsets) noexcept {
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

const SourceManager::LineDirectiveInfo* SourceManager::FileInfo::getPreviousLineDirective(
    size_t rawLineNumber) const {

    if (lineDirectives.empty())
        return nullptr;

    auto it = std::ranges::lower_bound(lineDirectives, rawLineNumber, {},
                                       &LineDirectiveInfo::lineInFile);

    // lower_bound will give us an iterator to the first directive after the command
    // let's instead get a pointer to the one right before it
    if (it == lineDirectives.begin()) {
        if (it->lineInFile == rawLineNumber)
            return &(*it);
        return nullptr;
    }
    else {
        if (it == lineDirectives.end()) {
            // Check to see whether the actual last directive is before the
            // given line number
            if (lineDirectives.back().lineInFile >= rawLineNumber)
                return nullptr;
        }
        return &*(it - 1);
    }
}

} // namespace slang
