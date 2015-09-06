#include <fstream>

#include "slang.h"

namespace fs = std::tr2::sys;

namespace {

// TODO: remove this once canonical() is fixed in <filesystem>
fs::path canonicalWorkaround(const fs::path& path) {
    std::deque<fs::path> stack;
    for (auto& e : path) {
        const wchar_t* cstr = e.c_str();
        if (cstr[0] == '.' && cstr[1] == '.' && cstr[2] == '\0')
            stack.pop_back();
        else
            stack.push_back(e);
    }

    fs::path result;
    for (auto& e : stack)
        result /= e;

    return result;
}

}

namespace slang {

FileTracker::FileTracker() {
    workingDir = fs::current_path();

    // add a dummy entry to the start of the directory list so that our file IDs line up
    fileToDirectory.push_back(nullptr);
}

std::string FileTracker::makeAbsolutePath(StringRef path) const {
    if (!path)
        return "";

    return (workingDir / path_type(path.begin(), path.end())).string();
}

void FileTracker::addSystemDirectory(StringRef path) {
    systemDirectories.emplace_back(path.begin(), path.end());
}

void FileTracker::addUserDirectory(StringRef path) {
    userDirectories.emplace_back(path.begin(), path.end());
}

FileID FileTracker::track(StringRef path) {
    auto it = pathMap.find(path);
    if (it != pathMap.end())
        return it->second;

    FileID result = FileID::get(nextFileID++);
    pathMap[path.intern(alloc)] = result;

    fileToDirectory.push_back(nullptr);

    return result;
}

bool FileTracker::readSource(StringRef fileName, SourceFile& file) {
    // ensure that we have an absolute path
    ASSERT(fileName);
    path_type absPath = fs::absolute(path_type(fileName.begin(), fileName.end()), workingDir);

    // load the file
    if (!openFile(absPath, file.buffer))
        return false;

    // assign a file ID
    file.id = track(absPath.string());
    cacheDirectory(std::move(absPath), file.id);

    return true;
}

SourceFile* FileTracker::readHeader(FileID currentSource, StringRef path, bool systemPath) {
    // if the header is specified as an absolute path, just do a straight lookup
    ASSERT(path);
    path_type p(path.begin(), path.end());
    if (p.is_absolute())
        return openCached(p);

    // system path lookups only look in system directories
    if (systemPath) {
        for (auto& d : systemDirectories) {
            SourceFile* result = openCached(d / p);
            if (result)
                return result;
        }
        return nullptr;
    }

    // search relative to the current file
    const path_type* dir = fileToDirectory[currentSource.getValue()];
    if (!dir)
        return nullptr;
    
    SourceFile* result = openCached((*dir) / p);
    if (result)
        return result;

    // search additional include directories
    for (auto& d : userDirectories) {
        result = openCached(d / p);
        if (result)
            return result;
    }

    return nullptr;
}

SourceFile* FileTracker::openCached(path_type fullPath) {
    // first see if we have this cached
    fullPath = canonicalWorkaround(fullPath);
    auto canonicalStr = fullPath.string();
    auto it = lookupCache.find(canonicalStr);
    if (it != lookupCache.end())
        return it->second.get();

    // do the read
    Buffer<char> buffer(0);
    if (!openFile(fullPath, buffer)) {
        lookupCache.emplace(std::move(canonicalStr), nullptr);
        return nullptr;
    }

    // cache the results
    FileID id = track(canonicalStr);
    auto result = lookupCache.emplace(std::move(canonicalStr), std::make_unique<SourceFile>(id, std::move(buffer)));

    cacheDirectory(std::move(fullPath), id);
    return result.first->second.get();
}

bool FileTracker::openFile(const path_type& path, Buffer<char>& buffer) {
    std::error_code ec;
    uintmax_t size = fs::file_size(path, ec);
    if (ec || size > INT32_MAX)
        return false;

    buffer.extend((uint32_t)size);
    std::ifstream stream(path);
    stream.read(buffer.begin(), size);

    return true;
}

void FileTracker::cacheDirectory(path_type path, FileID file) {
    fileToDirectory[file.getValue()] = &*directories.insert(path.remove_filename()).first;
}

}