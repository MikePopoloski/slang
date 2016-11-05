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
#include "Buffer.h"
#include "StringRef.h"
#include "SyntaxNode.h"
#include "SyntaxTree.h"

namespace slang {

class Diagnostics;
class CompilationUnitSymbol;
class DesignElementSymbol;
struct MemberSyntax;
struct ModuleDeclarationSyntax;
struct HierarchyInstantiationSyntax;

/// The DeclarationTable merges a view of all modules (and interfaces and programs) in design scope.
/// It is used for three purposes:
///   1. Figure out which modules aren't instantiated and are therefore "top-level".
///   2. Allow instantiation of design elements from other files once we start binding the hierarchy.
///   3. Check if we have any defparam statements in the design.
class DeclarationTable {
public:
    DeclarationTable(ArrayRef<CompilationUnitSymbol*> compilationUnits, Diagnostics& diagnostics);

    DesignElementSymbol* findSymbol(StringRef name) const;
    bool anyDefParams() const { return hasDefParams; }

private:
    using NameSet = std::unordered_set<StringRef>;
    void visit(const ModuleDeclarationSyntax* module, std::vector<NameSet>& scopeStack);
    void visit(const MemberSyntax* node, std::vector<NameSet>& scopeStack);
    static bool containsName(const std::vector<NameSet>& scopeStack, StringRef name);

    std::unordered_map<StringRef, DesignElementSymbol*> nameLookup;
    bool hasDefParams = false;
};

}