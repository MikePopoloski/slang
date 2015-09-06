#include "slang.h"

#ifdef PLATFORM_WINDOWS

#include <Windows.h>

namespace slang {

class WindowsFileSystem : public IFileSystem {
public:
    WindowsFileSystem() {
        // add dummy entry to directory list so that IDs align
        directories.push_back(DirectoryEntry());
    }

    bool readFile(StringRef path, Buffer<char>& buffer) override final {
        if (path.empty() || path.length() >= MAX_PATH)
            return false;

        char pathBuffer[MAX_PATH];
        memcpy(pathBuffer, path.begin(), path.length());
        pathBuffer[path.length()] = '\0';

        return readFileInternal(pathBuffer, buffer);
    }

    bool readFile(DirectoryID directory, StringRef fileName, Buffer<char>& buffer) override final {
        if (!directory.valid() || fileName.empty())
            return false;

        DirectoryEntry& entry = directories[getValue(directory)];

        if (entry.pathLength + fileName.length() >= MAX_PATH)
            return false;

        char pathBuffer[MAX_PATH];
        memcpy(pathBuffer, entry.path, entry.pathLength);
        memcpy(&pathBuffer[entry.pathLength], fileName.begin(), fileName.length());
        pathBuffer[entry.pathLength + fileName.length()] = '\0';

        return readFileInternal(pathBuffer, buffer);
    }

    bool isPathAbsolute(StringRef path) override final {
        ASSERT(!path.empty());

        const char* str = path.begin();
        char first = *str++;
        if (first == '/' || first == '\\')
            return false;

        // keep walking the string until we find:
        // 1) a ':', which is a drive separator
        // 2) a '/' or '\', which are path separators and therefore not absolute
        // 3) a '.', either an extension or a ../ specifier
        // 4) end of string, which means relative
        while (str != path.end()) {
            char c = *str++;
            switch (c) {
                case '\0':
                case '/':
                case '\\':
                case '.':
                    return false;
                case ':':
                    return true;
            }
        }
        return false;
    }

    DirectoryID walkPath(StringRef* path) override final {
        ASSERT(path);

        return DirectoryID();
    }

private:
    struct DirectoryEntry {
        char path[MAX_PATH];
        int pathLength;
    };
    std::deque<DirectoryEntry> directories;

    bool readFileInternal(const char* fullPath, Buffer<char>& buffer) {
        HANDLE handle = CreateFileA(
            fullPath,
            GENERIC_READ,
            FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
            NULL,
            OPEN_EXISTING,
            FILE_FLAG_SEQUENTIAL_SCAN,
            NULL
            );

        if (handle == INVALID_HANDLE_VALUE)
            return false;

        // we only support files up to Int32 max size
        LARGE_INTEGER largeInt;
        if (!GetFileSizeEx(handle, &largeInt) || largeInt.QuadPart > INT32_MAX) {
            CloseHandle(handle);
            return false;
        }

        uint32_t size = (uint32_t)largeInt.QuadPart;
        buffer.ensureSize(size);

        DWORD read;
        BOOL result = ReadFile(handle, buffer.begin(), size, &read, NULL);

        CloseHandle(handle);
        return result && read == size;
    }
};

IFileSystem& getOSFileSystem() {
    static WindowsFileSystem* fs = new WindowsFileSystem();
    return *fs;
}

}

#endif