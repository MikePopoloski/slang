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
    void addIncludeDir(const string& dir) {
        sourceManager.addUserDirectory(StringRef(dir));
    }

    void parseFile(const string& path) {
        currentFile = StringRef(path);
        SyntaxTree tree = SyntaxTree::fromFile(currentFile, sourceManager);
        visitNode(&tree.root());

        //printf("%s", tree.reportDiagnostics().c_str());
        //printf("%s", tree.root().toString(SyntaxToStringFlags::IncludePreprocessed | SyntaxToStringFlags::IncludeTrivia).c_str());
    }

    void visit(const ModuleHeaderSyntax& header) {
        StringRef name = header.name.valueText();
        if (name) {
            auto pair = declToFile.try_emplace(name, currentFile);
            if (!pair.second) {
                printf("Duplicate declaration: %s (%s, %s)\n",
                       name.toString().c_str(), currentFile.toString().c_str(),
                       pair.first->second.toString().c_str());
            }
        }
    }

    void visit(const HierarchyInstantiationSyntax& instantiation) {
        StringRef name = instantiation.type.valueText();
        if (name)
            fileToDeps[currentFile].insert(name);
    }

    void visit(const PackageImportItemSyntax& packageImport) {
        StringRef name = packageImport.package.valueText();
        if (name)
            fileToDeps[currentFile].insert(name);
    }

    void printDeps() {
        for (const auto& fileAndSet : fileToDeps) {
            StringRef file = fileAndSet.first;
            for (const auto& dep : fileAndSet.second) {
                auto it = declToFile.find(dep);
                if (it == declToFile.end())
                    printf("Couldn't find decl: %s\n", dep.toString().c_str());
                else if (it->second != file)
                    printf("%s: %s\n", file.toString().c_str(), it->second.toString().c_str());
            }
        }
    }

private:
    SourceManager sourceManager;
    StringRef currentFile;

    // Map from source element (module declaration, package declaration) to file.
    std::unordered_map<StringRef, StringRef> declToFile;

    // Map from file to a dependency (via a module instantiation or package reference).
    std::unordered_map<StringRef, std::unordered_set<StringRef>> fileToDeps;
};

int main(int argc, char* argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: slang-depmap [directories...]\n");
        return 1;
    }

    // Find all Verilog files in the given directories.
    DependencyMapper mapper;
    vector<Path> verilogFiles;
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
            verilogFiles = findFiles(argv[i], ".sv", true);
        }
    }

    // Parse each file, build a map of top-level module, interface, and
    // package definitions.
    for (const Path& path : verilogFiles)
        mapper.parseFile(path.str());

    mapper.printDeps();
}
