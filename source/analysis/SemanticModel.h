////------------------------------------------------------------------------------
//// SemanticModel.h
//// Symbol binding and semantic analysis.
////
//// File is under the MIT license; see LICENSE for details.
////------------------------------------------------------------------------------
//#pragma once
//
//#include <deque>
//#include <functional>
//#include <memory>
//#include <unordered_map>
//#include <vector>
//
//#include "diagnostics/Diagnostics.h"
//#include "parsing/AllSyntax.h"
//#include "util/BumpAllocator.h"
//#include "util/HashMap.h"
//#include "util/SmallVector.h"
//
//#include "BoundNodes.h"
//#include "DeclarationTable.h"
//#include "Binder.h"
//#include "Symbol.h"
//
//namespace slang {
//
///// SemanticModel is responsible for binding symbols and performing
///// type checking based on input parse trees.
//class SemanticModel {
//public:
//    /// This constructor is a shortcut for cases where you don't need to do
//    /// a full compile; the full compilation process needs a declaration table
//    /// and presumably multiple syntax trees.
//    explicit SemanticModel(SyntaxTree& tree);
//
//    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable);
//
//    const TypeSymbol& getType(const DataTypeSyntax& syntax, const ScopeSymbol& scope);
//    const SubroutineSymbol& getSubroutine(const FunctionDeclarationSyntax& syntax, const ScopeSymbol& scope);
//
//	SymbolList getMembers(const SyntaxList<MemberSyntax>& members, const Symbol& parent);
//
//    void makeVariables(const DataDeclarationSyntax& syntax, SmallVector<const Symbol*>& results, ScopeSymbol* scope);
//
//    /// Utilities for getting various common type symbols.
//    const TypeSymbol& getErrorType() const { return getKnownType(SyntaxKind::Unknown); }
//    const TypeSymbol& getKnownType(SyntaxKind kind) const;
//    const TypeSymbol& getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false);
//
//    BumpAllocator& getAllocator() { return alloc; }
//    Diagnostics& getDiagnostics() { return diagnostics; }
//
//	ConstantValue evaluateConstant(const ExpressionSyntax& syntax, const ScopeSymbol& scope);
//	ConstantValue evaluateConstantAndConvert(const ExpressionSyntax& syntax, const TypeSymbol& type, const ScopeSymbol& scope);
//
//
//
//	// Small collection of info extracted from a parameter definition
//	struct ParameterInfo {
//		const ParameterDeclarationSyntax& paramDecl;
//		const VariableDeclaratorSyntax& declarator;
//		StringRef name;
//		SourceLocation location;
//		ExpressionSyntax* initializer;
//		bool local;
//		bool bodyParam;
//	};
//
//	Diagnostic& addError(DiagCode code, SourceLocation location);
//	const std::vector<ParameterInfo>& getDeclaredParams(const ModuleDeclarationSyntax& syntax);
//
//	template<typename T, typename... Args>
//	T& allocate(Args&&... args) {
//		return *alloc.emplace<T>(std::forward<Args>(args)...);
//	}
//
//    void handleVariableDeclarator(const VariableDeclaratorSyntax& syntax, SmallVector<const Symbol *>& results, Scope *scope, const VariableSymbol::Modifiers &modifiers, const TypeSymbol *typeSymbol);
//
//private:
//    
//
//    // Gets the parameters declared in the module, with additional information about whether
//    // they're public or not. These results are cached in `parameterCache`.
//    const std::vector<ParameterInfo>& getModuleParams(const ModuleDeclarationSyntax& syntax);
//
//    // Helper function used by getModuleParams to convert a single parameter declaration into
//    // one or more ParameterInfo instances.
//    bool getParamDecls(const ParameterDeclarationSyntax& syntax, std::vector<ParameterInfo>& buffer,
//                       HashMapBase<StringRef, SourceLocation>& nameDupMap,
//                       bool lastLocal, bool overrideLocal, bool bodyParam);
//
//    // Process attributes and convert them to a normalized form. No specific handling is done for attribute
//    // types, we just pull out their values here.
//    void getAttributes(SmallVector<const AttributeSymbol*>& results, const SyntaxList<AttributeInstanceSyntax>& attributes);
//
//    void handlePackageImport(const PackageImportDeclarationSyntax& syntax, Scope* scope);
//    void handleInstantiation(const HierarchyInstantiationSyntax& syntax, SmallVector<const Symbol*>& results, Scope* instantiationScope);
//    void handleDataDeclaration(const DataDeclarationSyntax& syntax, SmallVector<const Symbol *>& results, Scope* scope);
//    void handleProceduralBlock(const ProceduralBlockSyntax& syntax, SmallVector<const Symbol *>& results, const Scope* scope);
//    void handleIfGenerate(const IfGenerateSyntax& syntax, SmallVector<const Symbol*>& results, const Scope* scope);
//    void handleLoopGenerate(const LoopGenerateSyntax& syntax, SmallVector<const Symbol*>& results, const Scope* scope);
//    void handleGenerateBlock(const MemberSyntax& syntax, SmallVector<const Symbol*>& results, const Scope* scope);
//    void handleGenvarDecl(const GenvarDeclarationSyntax& syntax, SmallVector<const Symbol*>& results, const Scope* scope);
//    void handleGenerateItem(const MemberSyntax& syntax, SmallVector<const Symbol*>& results, Scope* scope);
//
//    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const Scope& scope);
//	SVInt coerceInteger(ConstantValue&& value, bool& bad);
//
//    const BoundExpression* bindInitializer(const VariableDeclaratorSyntax& syntax, const TypeSymbol* type, const Scope* scope);
//
//    BumpAllocator& alloc;
//    Diagnostics& diagnostics;
//    DeclarationTable& declTable;
//
//    HashMap<const ModuleDeclarationSyntax*, std::vector<ParameterInfo>> parameterCache;
//
//    // preallocated type symbols for known types
//    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;
//
//    // cache of simple integral types keyed by {width, signedness, 4-state, isReg}
//    std::unordered_map<uint64_t, const TypeSymbol*> integralTypeCache;
//
//    // An empty declaration table to make it easier to create SemanticModels
//    // where we don't care about the full compilation process.
//    static DeclarationTable EmptyDeclTable;
//
//    // ScriptSession calls internal parsing handlers on input snippets
//    friend class ScriptSession;
//};
//
//}
