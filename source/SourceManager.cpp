#include <fstream>
#include <deque>
#include <filesystem>
#include <unordered_map>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "StringRef.h"
#include "SourceManager.h"

namespace fs = std::tr2::sys;

namespace slang {

SourceManager::SourceManager() {
    workingDir = fs::current_path();

    // add a dummy entry to the start of the directory list so that our file IDs line up
    fileToDirectory.push_back(nullptr);
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

SourceBuffer* SourceManager::getBuffer(FileID id) {
	if (!id)
		return nullptr;

	ASSERT(id.id < fileToBuffer.size());
	return fileToBuffer[id.id];
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
	const path_type* dir = fileToDirectory[includedFrom.getValue()];
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

	// cache the directory
	fileToDirectory.push_back(&*directories.insert(fullPath.remove_filename()).first);

	// cache the file
	FileID id = FileID::get(nextFileID++);
	auto result = lookupCache.emplace(std::move(canonicalStr), std::make_unique<SourceBuffer>(id, std::move(buffer))).first->second.get();
	fileToBuffer.push_back(result);

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

}