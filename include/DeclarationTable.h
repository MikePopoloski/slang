#pragma once

#include <deque>
#include <unordered_map>

#include "ArrayRef.h"
#include "Buffer.h"
#include "StringRef.h"
#include "SyntaxNode.h"
#include "SyntaxTree.h"

namespace slang {

struct MemberSyntax;
struct ModuleDeclarationSyntax;
struct HierarchyInstantiationSyntax;

/// A DeclarationTable keeps a view of all modules in design scope.
/// It is used for two purposes:
///   1. Figure out which modules aren't instantiated and are therefore "top-level".
///   2. Allow instantiation of modules from other files once we start binding the hierarchy.
class DeclarationTable {
public:
    void addSyntaxTree(const SyntaxTree* tree);

    ArrayRef<ModuleDeclarationSyntax*> getTopLevelModules(Diagnostics& diagnostics);

private:
    // Track each compilation unit's declarations separately and then merge them
    // once we have them all. This allows parallelizing the search process.
    struct UnitDecls {
        Buffer<ModuleDeclarationSyntax*> rootNodes;
        Buffer<HierarchyInstantiationSyntax*> instantiations;
        bool hasDefParams;
    };

    struct DeclAndFlag {
        ModuleDeclarationSyntax* decl;
        bool instantiated = false;

        DeclAndFlag(ModuleDeclarationSyntax* decl) : decl(decl) {}
    };

    using NameList = std::deque<StringRef>;
    static void visit(ModuleDeclarationSyntax* module, UnitDecls& unit, std::deque<NameList>& scopeStack);
    static void visit(MemberSyntax* node, UnitDecls& unit, std::deque<NameList>& scopeStack);
    static bool containsName(const std::deque<NameList>& scopeStack, StringRef name);

    Buffer<UnitDecls> units;
    std::unordered_map<StringRef, DeclAndFlag> nameLookup;
    Buffer<ModuleDeclarationSyntax*> topLevelModules;
    bool dirty = false;
};

}