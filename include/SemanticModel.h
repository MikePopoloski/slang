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

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    /// This constructor is a shortcut for cases where you don't need to do
    /// a full compile; the full compilation process needs a declaration table
    /// and presumably multiple syntax trees.
    explicit SemanticModel(SyntaxTree& tree);

    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable);

    void makePackages();
    InstanceSymbol* makeImplicitInstance(const ModuleDeclarationSyntax* syntax, Scope *definitions = nullptr);
    const TypeSymbol* makeTypeSymbol(const DataTypeSyntax* syntax, Scope* scope);
    const SubroutineSymbol* makeSubroutine(const FunctionDeclarationSyntax* syntax, Scope* scope);

    void makeVariables(const DataDeclarationSyntax* syntax, SmallVector<const Symbol*>& results, Scope* scope);

    /// Utilities for getting various common type symbols.
    const TypeSymbol* getErrorType() const { return getKnownType(SyntaxKind::Unknown); }
    const TypeSymbol* getKnownType(SyntaxKind kind) const;
    const TypeSymbol* getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false);

    BumpAllocator& getAllocator() { return alloc; }
    Diagnostics& getDiagnostics() { return diagnostics; }
    const Scope* getPackages() { return &packages; }

    const Scope* getSystemScope() { return &systemScope; }

    void handleVariableDeclarator(const VariableDeclaratorSyntax *syntax, SmallVector<const Symbol *>& results, Scope *scope, const VariableSymbol::Modifiers &modifiers, const TypeSymbol *typeSymbol);

private:
    // Small collection of info extracted from a parameter definition
    struct ParameterInfo {
        const ParameterDeclarationSyntax* paramDecl;
        const VariableDeclaratorSyntax* declarator;
        StringRef name;
        SourceLocation location;
        ExpressionSyntax* initializer;
        bool local;
        bool bodyParam;
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
    void evaluateParameter(ParameterSymbol* symbol, const ExpressionSyntax* initializer, Scope* scope);

    // Uses a module declaration and an optional set of parameter assignments to create all of the
    // evaluated parameter symbols for a particular module instance. Note that these parameter symbols
    // can potentially be shared by instances if they are in the same declaration.
    void makePublicParameters(Scope* declScope, const ModuleDeclarationSyntax* decl,
                              const ParameterValueAssignmentSyntax* parameterAssignments,
                              Scope* instantiationScope, SourceLocation instanceLocation, bool isTopLevel);

    // Process attributes and convert them to a normalized form. No specific handling is done for attribute
    // types, we just pull out their values here.
    void makeAttributes(SmallVector<const AttributeSymbol*>& results, const SyntaxList<AttributeInstanceSyntax>& attributes);

    // Uses a instance declaration and instantiation scope
    // to create all interface objects for a particular module instance
    void makeInterfacePorts(Scope* scope, const ModuleDeclarationSyntax* instanceModuleSyntax, const HierarchicalInstanceSyntax* syntax, const Scope* instantiationScope, SourceLocation instanceLocation);

    // construct module symbol parametrized with per-instance scope with parameters and port-interfaces symbols
    const ModuleSymbol* makeModule(const ModuleDeclarationSyntax* syntax, Scope *scope);

    void handlePackageImport(const PackageImportDeclarationSyntax* syntax, Scope* scope);
    void handleInstantiation(const HierarchyInstantiationSyntax* syntax, SmallVector<const Symbol*>& results, Scope* instantiationScope);
    void handleDataDeclaration(const DataDeclarationSyntax *syntax, SmallVector<const Symbol *>& results, Scope* scope);
    void handleProceduralBlock(const ProceduralBlockSyntax *syntax, SmallVector<const Symbol *>& results, const Scope* scope);
    void handleIfGenerate(const IfGenerateSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope);
    void handleLoopGenerate(const LoopGenerateSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope);
    void handleGenerateBlock(const MemberSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope);
    void handleGenvarDecl(const GenvarDeclarationSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope);
    void handleGenerateItem(const MemberSyntax* syntax, SmallVector<const Symbol*>& results, Scope* scope);

    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const Scope* scope);

    const BoundExpression* bindInitializer(const VariableDeclaratorSyntax *syntax, const TypeSymbol* type, const Scope* scope);
    const BoundExpression* bindConstantExpression(const ExpressionSyntax* syntax, const Scope* scope);
    ConstantValue evaluateConstant(const ExpressionSyntax* syntax, const Scope* scope);
    static ConstantValue evaluateConstant(const BoundExpression* tree);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    DeclarationTable& declTable;
    Scope packages;
    Scope systemScope;

    HashMap<const ModuleDeclarationSyntax*, std::vector<ParameterInfo>> parameterCache;

    // preallocated type symbols for known types
    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // cache of simple integral types keyed by {width, signedness, 4-state, isReg}
    std::unordered_map<uint64_t, const TypeSymbol*> integralTypeCache;

    // An empty declaration table to make it easier to create SemanticModels
    // where we don't care about the full compilation process.
    static DeclarationTable EmptyDeclTable;

    // ScriptSession calls internal parsing handlers on input snippets
    friend class ScriptSession;
};

}
