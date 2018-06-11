// SystemVerilog dependency mapping tool
// This tool takes a list of directories, finds all SystemVerilog files within those directories,
// and produces a map of dependencies for use with build systems.

#include <cstdlib>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parsing/SyntaxTree.h"
#include "parsing/SyntaxVisitor.h"

using namespace slang;

class DependencyMapper : public SyntaxVisitor<DependencyMapper> {
public:
    void addIncludeDir(const std::string& dir) {
        sourceManager.addUserDirectory(string_view(dir));
    }

    void parseFile(const std::string& path) {
        currentFile = path;
        auto tree = SyntaxTree::fromFile(currentFile, sourceManager);
        //visitNode(&tree->root());

        printf("%s", tree->reportDiagnostics().c_str());
        //printf("%s", tree->root().toString(SyntaxToStringFlags::IncludePreprocessed | SyntaxToStringFlags::IncludeTrivia).c_str());
    }

    void visit(const ModuleHeaderSyntax& header) {
        std::string name { header.name.valueText() };
        if (!name.empty()) {
            auto pair = declToFile.try_emplace(name, currentFile);
            if (!pair.second) {
                printf("Duplicate declaration: %s (%s, %s)\n",
                       name.c_str(), currentFile.c_str(),
                       pair.first->second.c_str());
            }
        }
    }

    void visit(const HierarchyInstantiationSyntax& instantiation) {
        std::string name { instantiation.type.valueText() };
        if (!name.empty())
            fileToDeps[currentFile].insert(name);
    }

    void visit(const PackageImportItemSyntax& packageImport) {
        std::string name { packageImport.package.valueText() };
        if (!name.empty())
            fileToDeps[currentFile].insert(name);
    }

    void printDeps() {
        for (const auto& fileAndSet : fileToDeps) {
            const std::string& file = fileAndSet.first;
            for (const auto& dep : fileAndSet.second) {
                auto it = declToFile.find(dep);
                if (it == declToFile.end())
                    printf("Couldn't find decl: %s\n", dep.c_str());
                else if (it->second != file)
                    printf("%s: %s\n", file.c_str(), it->second.c_str());
            }
        }
    }

private:
    SourceManager sourceManager;
    std::string currentFile;

    // Map from source element (module declaration, package declaration) to file.
    std::unordered_map<std::string, std::string> declToFile;

    // Map from file to a dependency (via a module instantiation or package reference).
    std::unordered_map<std::string, std::unordered_set<std::string>> fileToDeps;
};

int main(int argc, char* argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: slang-depmap [directories...]\n");
        return 1;
    }

    // Find all Verilog files in the given directories.
    DependencyMapper mapper;
    std::vector<fs::path> verilogFiles;
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
            for (auto& entry : fs::recursive_directory_iterator(argv[i])) {
                if (entry.is_regular_file() && entry.path().filename().extension() == ".sv")
                    verilogFiles.push_back(entry.path());
            }
        }
    }

    // Parse each file, build a map of top-level module, interface, and
    // package definitions.
    for (const fs::path& path : verilogFiles)
        mapper.parseFile(path.string());

    mapper.printDeps();
}
