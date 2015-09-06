#include "catch.hpp"
#include "slang.h"

using namespace slang;

TEST_CASE("Absolute paths", "[files]") {
    IFileSystem& fs = getOSFileSystem();
    CHECK(fs.isPathAbsolute("C:/foo\\stuff.txt"));
    CHECK(fs.isPathAbsolute("\\\\server\\sharename\\"));
    CHECK(!fs.isPathAbsolute("stuff"));
    CHECK(!fs.isPathAbsolute("..\\stuff.txt"));
}

TEST_CASE("Open file (absolute)", "[files]") {
    IFileSystem& fs = getOSFileSystem();

    Buffer<char> buffer;
    CHECK(!fs.readFileAbsolute("X:\\nonsense.txt", buffer));
    CHECK(fs.readFileAbsolute("C:\\Users\\mike\\Desktop\\slang\\tests\\data\\include.svh", buffer));
    CHECK(buffer.count() > 0);
}