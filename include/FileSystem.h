#pragma once

namespace slang {

class IFileSystem;

struct DirectoryID : public HandleBase<DirectoryID> {
    friend class IFileSystem;
};

class IFileSystem {
public:
    virtual ~IFileSystem() {}

    // open the given file and read its entire contents into buffer
    // returns false if file not found
    virtual bool readFile(StringRef path, Buffer<char>& buffer) = 0;

    // reads a file relative to the given directory
    virtual bool readFile(DirectoryID directory, StringRef fileName, Buffer<char>& buffer) = 0;

    // check whether the path is absolute or relative
    virtual bool isPathAbsolute(StringRef path) = 0;

    // get the first directory in a given path
    // the path is modified to strip off that leading directory name
    // if there is no directory info in the path, returns an invalid directory ID
    virtual DirectoryID walkPath(StringRef* path) = 0;

    // gets the deepest directory in a path
    DirectoryID getDeepestDirectory(StringRef path) {
        DirectoryID last;
        while (true) {
            DirectoryID next = walkPath(&path);
            if (!next.valid())
                return last;

            last = next;
        }
    }

protected:
    static uint32_t getValue(DirectoryID directory) {
        return directory.getValue();
    }
};

IFileSystem& getOSFileSystem();

}