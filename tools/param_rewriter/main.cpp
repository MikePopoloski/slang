#include <cstdlib>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "slang.h"
#include "Symbol.h"
#include "SyntaxVisitor.h"

using namespace slang;
using namespace std;

BumpAllocator alloc;


Token identifier(const std::string& name, ArrayRef<Trivia> trivia) {
    StringRef text { name };
    auto info = alloc.emplace<Token::Info>(trivia, text.intern(alloc), SourceLocation(), 0);
    info->extra = IdentifierType::Normal;
    return Token(TokenKind::Identifier, info);
}

// void walkChildren(const ModuleSymbol* module, unordered_set<BufferID>& visitedFiles,
//                   ModuleLookup& moduleLookup) {

//     for (auto child : module->children) {
//         if (child->kind == SymbolKind::Instance) {
//             const ModuleSymbol* module = child.as<InstanceSymbol>().module;
//             auto& permutations = moduleLookup[module->syntax];

//             // See if we've written this permutation already
//             ParamKey key { module };
//             if (permutations.insert(key).second) {
//                 writeModule(module, key);
//             }
//         }
//     }
// }

class ModuleRewriter : public SyntaxVisitor<ModuleRewriter> {
public:
    void registerInstance(const InstanceSymbol* instance) {
        instanceToModule[instance->syntax] = instance->module;
        for (auto child : instance->module->children) {
            if (child->kind == SymbolKind::Instance)
                registerInstance((const InstanceSymbol*)child);
        }
    }

    void run(SyntaxTree& tree) {
        auto syntax = tree.root();
        auto location = syntax->getFirstToken().location();
        bool visited = !visitedFiles.insert(location.buffer()).second;

        StringRef fileName = tree.sourceManager().getFileName(location);
        FILE* fp = fopen((fileName.toString() + "_rewrite").c_str(), visited ? "a" : "w");
        ASSERT(fp);

        buffer.clear();
        visitNode(syntax);

        fwrite(buffer.begin(), buffer.count(), 1, fp);
        fclose(fp);
    }

    // void visit(const ModuleDeclarationSyntax& module) {
    //     visitDefault(module);
    // }

    // void visit(const HierarchyInstantiationSyntax& instantiation) {
    //     auto module = sem.makeModule(instantiation);
    //     if (!module)
    //         visitDefault(instantiation);
    //     else {
    //         auto& permutations = moduleMap[module->syntax];
    //         auto& index = permutations[getParamString(module)];
    //         if (index == 0)
    //             index = permutations.size();

    //         HierarchyInstantiationSyntax newSyntax = module;
    //         newSyntax.name = identifier(module.name.toString() + index);
    //         visitDefault(newSyntax);
    //     }
    // }

    void visit(const HierarchyInstantiationSyntax& instantiation) {
        auto module = instanceToModule[&instantiation];
        if (!module)
            visitDefault(instantiation);
        else {
            auto& permutations = moduleMap[module->syntax];
            auto& index = permutations[getParamString(module)];
            if (index == 0)
                index = permutations.size();

            HierarchyInstantiationSyntax newSyntax = instantiation;
            newSyntax.parameters = nullptr;
            newSyntax.type = identifier(module->name.toString() + to_string(index),
                                        instantiation.type.trivia());
            visitDefault(newSyntax);
        }
    }

    void visitToken(Token t) {
        t.writeTo(buffer, SyntaxToStringFlags::IncludeTrivia);
    }

private:
    static string getParamString(const ModuleSymbol* module) {
        string result;
        for (auto child : module->children) {
            if (child->kind == SymbolKind::Parameter)
                result += child->as<ParameterSymbol>().value.integer().toString(LiteralBase::Decimal);
        }
        return result;
    }

    unordered_map<const HierarchyInstantiationSyntax*, const ModuleSymbol*> instanceToModule;
    unordered_map<const ModuleDeclarationSyntax*, unordered_map<string, size_t>> moduleMap;
    unordered_set<BufferID> visitedFiles;
    Vector<char> buffer;
//     DeclarationTable& declTable;
};

// void writeModule(const ModuleSymbol* module,
//                  SourceManager& sourceManager,
//                  unordered_set<BufferID>& visitedFiles,
//                  ModuleLookup& moduleLookup) {

//     // Keep track of which files we visit, and get a handle to the output.
//     const ModuleDeclarationSyntax* syntax = module->syntax;
//     auto location = syntax->getFirstToken().location();
//     bool visited = !visitedFiles.insert(location.buffer()).second;

//     StringRef fileName = sourceManager.getFileName(location);
//     FILE* fp = fopen((fileName.toString() + "_rewrite").c_str(), visited ? "a" : "w");
//     ASSERT(fp);

//     SmallVectorSized<const ParameterSymbol*, 8> params;
//     for (auto child : module->children) {
//         if (child->kind == SymbolKind::Parameter) {
//             const auto& param = child->as<ParameterSymbol>();
//             if (!param.isLocal)
//                 params.append(&param);
//         }
//     }

//     // If we have no public parameters, just output the original module
//     if (params.empty()) {
//         auto str = syntax->toString(SyntaxToStringFlags::IncludeTrivia);
//         fwrite(str.c_str(), str.length(), 1, fp);
//     }
//     else {
//         // Otherwise create a new module instance that has a tweaked tree
//         ModuleHeaderSyntax header = *syntax->header;
//         string newName = header.name.valueText().toString();
//         newName += moduleLookup[syntax].size();
//         header.name = identifier(newName);

//         ParameterPortListSyntax parameters = *header.parameters;
//         header.parameters = &parameters;

//         ModuleDeclarationSyntax m = *syntax;
//         m.header = &header;

//         auto str = m.toString(SyntaxToStringFlags::IncludeTrivia);
//         fwrite(str.c_str(), str.length(), 1, fp);
//     }
// }

int main(int argc, char* argv[]) {
    // Expect a set of files as command line arguments
    if (argc <= 1) {
        fprintf(stderr, "Expected files on command line to process\n");
        return 1;
    }

    static_assert(a != b, "Foo");

    int const c = COUNTER_READ(my_cnt);

    printf("%d %d %d\n", a, b, c);

    // Parse each file and find declarations
    Diagnostics diagnostics;
    DeclarationTable declTable(diagnostics);

    vector<SyntaxTree> syntaxTrees;
    for (int i = 1; i < argc; i++) {
        StringRef fileName { argv[i], (uint32_t)strlen(argv[i]) };
        syntaxTrees.emplace_back(SyntaxTree::fromFile(fileName));

        auto& tree = syntaxTrees.back();
        if (!tree.diagnostics().empty())
            fprintf(stderr, "%s\n", tree.reportDiagnostics().c_str());

        declTable.addSyntaxTree(&tree);
    }

    // Do semantic analysis on each module to figure out parameter values
    ModuleRewriter rewriter;
    SemanticModel sem { alloc, diagnostics, declTable };
    for (auto module : declTable.getTopLevelModules()) {
        auto instance = sem.makeImplicitInstance(module);
        rewriter.registerInstance(instance);
    }

    // Now go through each syntax tree that we parsed and rewrite them to new files
    for (auto& tree : syntaxTrees)
        rewriter.run(tree);
}
