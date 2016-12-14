//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "BumpAllocator.h"
#include "DeclarationTable.h"
#include "Diagnostics.h"
#include "ExpressionBinder.h"
#include "HashMap.h"
#include "Scope.h"
#include "SmallVector.h"
#include "Symbol.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable);

    InstanceSymbol* makeImplicitInstance(const ModuleDeclarationSyntax* syntax);

    const TypeSymbol* makeTypeSymbol(const DataTypeSyntax* syntax, const Scope* scope);

    /// Utilities for getting various common type symbols.
    const TypeSymbol* getErrorType() const { return getKnownType(SyntaxKind::Unknown); }
    const TypeSymbol* getKnownType(SyntaxKind kind) const;
    const TypeSymbol* getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false);

    // Generalized symbol lookup based on the current scope stack.
    const Symbol* lookupSymbol(StringRef name, const Scope* scope);

    BumpAllocator& getAllocator() { return alloc; }
    Diagnostics& getDiagnostics() { return diagnostics; }

private:
    // Represents a simple constant range.
    struct ConstantRange {
        SVInt msb;
        SVInt lsb;
    };

    // Small collection of info extracted from a parameter definition
    struct ParameterInfo {
        const ParameterDeclarationSyntax* paramDecl;
        StringRef name;
        SourceLocation location;
        ExpressionSyntax* initializer;
        bool local;
        bool bodyParam;
    };

    // Small collection of info tied to a module/interface/program declaration
    struct ModuleDeclInfo {
        ;
        const Scope* scope;
    };

    // Gets the parameters declared in the module, with additional information about whether
    // they're public or not. These results are cached in `parameterCache`.
    const std::vector<ParameterInfo>& getModuleParams(const ModuleDeclarationSyntax* syntax);

    // Helper function used by getModuleParams to convert a single parameter declaration into
    // one or more ParameterInfo instances.
    bool getParamDecls(const ParameterDeclarationSyntax* syntax, std::vector<ParameterInfo>& buffer,
                       HashMapBase<StringRef, SourceLocation>& nameDupMap,
                       bool lastLocal, bool overrideLocal, bool bodyParam);

    // Evaluates an individual parameter using its initializer. This also finalizes its type.
    void evaluateParameter(ParameterSymbol* symbol, const ExpressionSyntax* initializer, const Scope* scope);

    // Uses a module declaration and an optional set of parameter assignments to create all of the
    // evaluated parameter symbols for a particular module instance. Note that these parameter symbols
    // can potentially be shared by instances if they are in the same declaration.
    void makeParameters(SmallVector<const ParameterSymbol*>& results, const ModuleDeclarationSyntax* decl,
                        const ParameterValueAssignmentSyntax* parameterAssignments,
                        const Scope* instantiationScope, SourceLocation instanceLocation, bool isTopLevel);

    const ModuleSymbol* makeModule(const ModuleDeclarationSyntax* syntax, ArrayRef<const ParameterSymbol*> parameters);

    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const Scope* scope);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    DeclarationTable& declTable;

    HashMap<const ModuleDeclarationSyntax*, std::vector<ParameterInfo>> parameterCache;

    // preallocated type symbols for known types
    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // cache of simple integral types keyed by {width, signedness, 4-state, isReg}
    std::unordered_map<uint64_t, const TypeSymbol*> integralTypeCache;
};

}