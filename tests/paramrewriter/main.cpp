#include <cstdlib>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "analysis/Symbol.h"
#include "parsing/SyntaxTree.h"
#include "parsing/SyntaxVisitor.h"

using namespace slang;
using namespace std;

BumpAllocator alloc;

Token identifier(const std::string& name, span<Trivia const> trivia) {
    string_view text{ name };
    auto info = alloc.emplace<Token::Info>(trivia, alloc.makeCopy(text), SourceLocation(), 0);
    info->extra = IdentifierType::Normal;
    return Token(TokenKind::Identifier, info);
}

class ModuleRewriter : public SyntaxVisitor<ModuleRewriter> {
public:
    void registerInstance(const ModuleInstanceSymbol&) {
        /*instanceToModule[&instance.syntax] = instance.module;
        syntaxToModules[&instance.module.syntax].push_back(instance.module);
        for (auto child : instance.module.members()) {
            if (child->kind == SymbolKind::Instance)
                registerInstance((const ModuleInstanceSymbol*)child);
        }*/
    }

    void run(SyntaxTree& tree) {
        const auto& syntax = tree.root();
        auto location = syntax.getFirstToken().location();
        bool visited = !visitedFiles.insert(location.buffer()).second;

        string_view fileName = tree.sourceManager().getFileName(location);
        FILE* fp = fopen((string(fileName) + "_rewrite").c_str(), visited ? "ab" : "wb");
        ASSERT(fp);

        buffer.clear();
        visitNode(&syntax);

        fwrite(buffer.begin(), buffer.size(), 1, fp);
        fclose(fp);
    }

    void visit(const ModuleDeclarationSyntax& syntax) {
        auto& list = syntaxToModules[&syntax];
        if (list.empty()) {
            visitDefault(syntax);
            return;
        }

        /*for (auto module : list) {
            SmallVectorSized<const ParameterSymbol*, 8> params;
            for (auto child : module->members()) {
                if (child->kind == SymbolKind::Parameter) {
                    const auto& param = child->as<ParameterSymbol>();
                    declToParam[&param.declarator] = &param;
                }
            }

            auto& permutations = moduleMap[&module->syntax];
            auto& index = permutations[getParamString(module)];
            if (index == 0)
                index = permutations.size();*/

            // Otherwise create a new module instance that has a tweaked tree
           /* ModuleHeaderSyntax header = syntax.header;
            string newName = header.name.valueText().toString();
            newName += to_string(index);
            header.name = identifier(newName, header.name.trivia());

            ModuleDeclarationSyntax m = syntax;
            m.header = header;
            visitDefault(m);

            if (module != list.back()) {
                buffer.append('\n');
                buffer.append('\n');
            }*/
        //}
    }

    void visit(const VariableDeclaratorSyntax& declarator) {
        auto param = declToParam[&declarator];
        if (!param) {
            visitDefault(declarator);
            return;
        }

        /*VariableDeclaratorSyntax newDecl = declarator;
        newDecl.initializer = nullptr;
        visitDefault(newDecl);*/

        buffer.appendRange(string_view(" = "));
//        buffer.appendRange(param->value.integer().toString(LiteralBase::Decimal));
    }

    void visit(const HierarchyInstantiationSyntax& instantiation) {
        auto module = instanceToModule[&instantiation];
        if (!module)
            visitDefault(instantiation);
        else {
            /*auto& permutations = moduleMap[&module->syntax];
            auto& index = permutations[getParamString(module)];
            if (index == 0)
                index = permutations.size();*/

            /*HierarchyInstantiationSyntax newSyntax = instantiation;
            newSyntax.parameters = nullptr;
            newSyntax.type = identifier(module->name.toString() + to_string(index),
                instantiation.type.trivia());
            visitDefault(newSyntax);*/
        }
    }

    void visitToken(Token t) {
        t.writeTo(buffer, SyntaxToStringFlags::IncludeTrivia);
    }

private:
    static string getParamString(const ParameterizedModuleSymbol*) {
        string result;
        /*for (auto child : module->members()) {
            if (child->kind == SymbolKind::Parameter)
                result += child->as<ParameterSymbol>().value.integer().toString(LiteralBase::Decimal);
        }*/
        return result;
    }

    unordered_map<const HierarchyInstantiationSyntax*, const ModuleSymbol*> instanceToModule;
    unordered_map<const VariableDeclaratorSyntax*, const ParameterSymbol*> declToParam;
    unordered_map<const ModuleDeclarationSyntax*, vector<const ModuleSymbol*>> syntaxToModules;
    unordered_map<const ModuleDeclarationSyntax*, unordered_map<string, size_t>> moduleMap;
    unordered_set<BufferID> visitedFiles;
    Vector<char> buffer;
};

int main(int argc, char* argv[]) {
    // Expect a set of files as command line arguments
    if (argc <= 1) {
        fprintf(stderr, "Expected files on command line to process\n");
        return 1;
    }

    // Parse each file and find declarations
    Diagnostics diagnostics;

    vector<SyntaxTree> syntaxTrees;
    for (int i = 1; i < argc; i++) {
        string_view fileName{ argv[i], (uint32_t)strlen(argv[i]) };
        syntaxTrees.emplace_back(SyntaxTree::fromFile(fileName));

        auto& tree = syntaxTrees.back();
        if (!tree.diagnostics().empty())
            fprintf(stderr, "%s\n", tree.reportDiagnostics().c_str());

        //declTable.addSyntaxTree(tree);
    }

    // Do semantic analysis on each module to figure out parameter values
    ModuleRewriter rewriter;
    //SemanticModel sem{ alloc, diagnostics, declTable };
    /*for (auto module : declTable.getTopLevelModules()) {
        auto instance = sem.makeImplicitInstance(*module);
        rewriter.registerInstance(instance);
    }*/

    // Now go through each syntax tree that we parsed and rewrite them to new files
    for (auto& tree : syntaxTrees)
        rewriter.run(tree);
}
