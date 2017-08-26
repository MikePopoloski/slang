// SystemVerilog dependency mapping tool
// This tool takes a list of directories, finds all SystemVerilog files within those directories,
// and produces a map of dependencies for use with build systems.

#include <cstdlib>
#include <string>
#include <vector>

#if defined(_WIN32)
#define NOMINMAX
#include <Windows.h>
#else
#include <dirent.h>
#endif

#include "parsing/SyntaxTree.h"

using namespace slang;
using namespace std;

void findVerilogFiles(const string& path, vector<string>& results) {
    vector<string> directories;

#if defined(_WIN32)
    WIN32_FIND_DATAA ffd;
    string base = path + "\\";
    HANDLE hFind = FindFirstFileA((base + "*").c_str(), &ffd);
    if (hFind == INVALID_HANDLE_VALUE)
        throw runtime_error("Internal error in FindFirstFile(): " + to_string(GetLastError()));

    do {
        if ((ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0) {
            // Handle files that end in '.sv'
            const char* ext = strrchr(ffd.cFileName, '.');
            if (ext && strcmp(ext, ".sv") == 0)
                results.push_back(base + ffd.cFileName);
        }
        else if (strcmp(ffd.cFileName, ".") != 0 && strcmp(ffd.cFileName, "..") != 0) {
            directories.push_back(base + ffd.cFileName);
        }
    } while (FindNextFileA(hFind, &ffd) != 0);

    DWORD dwError = GetLastError();
    if (dwError != ERROR_NO_MORE_FILES)
        throw runtime_error("Internal error in FindNextFile(): " + to_string(dwError));
    FindClose(hFind);
#else
    DIR* d;
    struct dirent* dir;
    string base = string(path) + "/";
    d = opendir(base.c_str());
    if (d) {
        while ((dir = readdir(d))) {
            if (dir->d_type == DT_REG) {
                // Handle files that end in '.sv'
                const char* ext = strrchr(dir->d_name, '.');
                if (ext && strcmp(ext, ".sv") == 0)
                    results.push_back(base + dir->d_name);
            }
            else if (strcmp(dir->d_name, ".") != 0 && strcmp(dir->d_name, "..") != 0) {
                directories.push_back(base + dir->d_name);
            }
        }
        closedir(d);
    }
#endif
    for (const auto& dir : directories)
        findVerilogFiles(dir.c_str(), results);
}

class DependencyMapper {
public:
    void addIncludeDir(const string& dir) {
        sourceManager.addUserDirectory(StringRef(dir));
    }

    void parseFile(const string& path) {
        SyntaxTree tree = SyntaxTree::fromFile(StringRef(path), sourceManager);
        printf("%s", tree.reportDiagnostics().c_str());

        printf("\n%s\n", tree.root().toString(SyntaxToStringFlags::IncludeTrivia | SyntaxToStringFlags::IncludePreprocessed).c_str());
    }

private:
    SourceManager sourceManager;
};

int main(int argc, char* argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: slang-depmap [directories...]\n");
        return 1;
    }

    // Find all Verilog files in the given directories.                
    DependencyMapper mapper;
    vector<string> verilogFiles;
    for (int i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
                case 'I':
                    mapper.addIncludeDir(argv[i] + 2);
                    break;
                default:
                    fprintf(stderr, "Unknown option: %s\n", argv[i]);
                    break;
            }
        }
        else {
            findVerilogFiles(argv[i], verilogFiles);
        }
    }

    // Parse each file, build a map of top-level module, interface, and
    // package definitions.                                            
    for (const string& path : verilogFiles)
        mapper.parseFile(path);
}
