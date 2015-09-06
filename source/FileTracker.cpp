#include <fstream>

#include "slang.h"

namespace fs = std::tr2::sys;

namespace slang {

FileTracker::FileTracker() {
    workingDir = fs::current_path();
}

FileID FileTracker::track(StringRef path) {
    auto it = pathMap.find(path);
    if (it != pathMap.end())
        return it->second;

    FileID result = FileID::get(nextFileID++);
    pathMap[path.intern(alloc)] = result;

    return result;
}

bool FileTracker::readSource(StringRef fileName, SourceFile& file) {
    // ensure that we have an absolute path
    ASSERT(fileName);
    fs::path absPath = fs::absolute(fs::path(fileName.begin(), fileName.end()), workingDir);

    // load the file
    if (!openFile(absPath, file.buffer))
        return false;

    // assign a file ID
    file.id = track(absPath.string());

    return true;
}

SourceFile* FileTracker::readHeader(FileID currentSource, StringRef path, bool systemPath) {
    return nullptr;
}

bool FileTracker::openFile(const fs::path& path, Buffer<char>& buffer) {
    std::error_code ec;
    uintmax_t size = fs::file_size(path, ec);
    if (ec || size > INT32_MAX)
        return false;

    buffer.extend((uint32_t)size);
    std::ifstream stream(path);
    stream.read(buffer.begin(), size);

    return true;
}

}