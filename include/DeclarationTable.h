//------------------------------------------------------------------------------
// DeclarationTable.h
// Module declaration tracking.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ArrayRef.h"
#include "SmallVector.h"
#include "StringRef.h"
#include "SyntaxNode.h"
#include "SyntaxTree.h"

namespace slang {

class Diagnostics;
struct MemberSyntax;
struct ModuleDeclarationSyntax;
struct HierarchyInstantiationSyntax;

///
/// The DeclarationTable merges a view of all modules (and interfaces and programs) in design scope.
/// It is used for three purposes:
///   1. Figure out which modules aren't instantiated and are therefore "top-level".
///   2. Allow instantiation of design elements from other files once we start binding the hierarchy.
///   3. Check if we have any defparam statements in the design.
///
/// This class is designed to be threadsafe.
///
class DeclarationTable {
public:
    DeclarationTable(Diagnostics& diagnostics);

    void addMember(const MemberSyntax *member);
    void addSyntaxTree(const SyntaxTree* tree);

    ArrayRef<const ModuleDeclarationSyntax*> getPackages();
    ArrayRef<const ModuleDeclarationSyntax*> getTopLevelModules();

    const ModuleDeclarationSyntax* find(StringRef name) const;

private:
    // Track each compilation unit's declarations separately and then merge them
    // once we have them all. This allows parallelizing the search process.
    struct UnitDecls {
        std::vector<const ModuleDeclarationSyntax*> rootNodes;
        std::vector<const HierarchyInstantiationSyntax*> instantiations;
        bool hasDefParams;
    };

    struct DeclAndFlag {
        const ModuleDeclarationSyntax* decl;
        bool instantiated = false;

        DeclAndFlag(const ModuleDeclarationSyntax* decl) : decl(decl) {}
    };

    using NameSet = std::unordered_set<StringRef>;
    static void visit(const ModuleDeclarationSyntax* module, UnitDecls& unit, std::vector<NameSet>& scopeStack);
    static void visit(const MemberSyntax* node, UnitDecls& unit, std::vector<NameSet>& scopeStack);
    static bool containsName(const std::vector<NameSet>& scopeStack, StringRef name);

    bool addRootNode(UnitDecls& unit, const MemberSyntax* member);

    Diagnostics& diagnostics;
    Vector<UnitDecls> units;
    Vector<const ModuleDeclarationSyntax*> packages;
    Vector<const ModuleDeclarationSyntax*> topLevel;
    std::unordered_map<StringRef, DeclAndFlag> nameLookup;
    bool dirty = false;
};

}
