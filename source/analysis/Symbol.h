//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <optional>
#include <vector>

#include "diagnostics/Diagnostics.h"
#include "numeric/SVInt.h"
#include "parsing/AllSyntax.h"
#include "text/SourceLocation.h"
#include "util/ArrayRef.h"
#include "util/HashMap.h"
#include "util/StringRef.h"

#include "ConstantValue.h"

namespace slang {

struct DataTypeSyntax;
struct ExpressionSyntax;
class BoundExpression;
class BoundStatement;
class BoundStatementList;
class Symbol;
class SyntaxTree;
class DesignRootSymbol;
class TypeSymbol;

using SymbolList = ArrayRef<const Symbol*>;

using Dimensions = ArrayRef<ConstantRange>;

enum class SymbolKind {
    Unknown,
    IntegralType,
    RealType,
    StringType,
    CHandleType,
    VoidType,
    EventType,
    EnumType,
    TypeAlias,
    Parameter,
    EnumValue,
    Module,
    Interface, // TODO: decouple interfaces from modules
    Modport,   // TODO: decouple interfaces from modules
    Program,
    Attribute,
    Genvar,
    GenerateBlock,
    ProceduralBlock,
    Variable,
    Instance,
    FormalArgument,
    Subroutine
};

/// Specifies the storage lifetime of a variable.
enum class VariableLifetime {
    Automatic,
    Static
};

/// Specifies behavior of an argument passed to a subroutine.
enum class FormalArgumentDirection {
    In,
    Out,
    InOut,
    Ref,
    ConstRef
};

/// Indicates which built-in system function is represented by a symbol.
enum class SystemFunction {
    Unknown,
    clog2,
    bits,
    left,
    right,
    low,
    high,
    size,
    increment
};

/// Base class for all symbols (logical code constructs) such as modules, types,
/// functions, variables, etc.
class Symbol {
public:
	/// The type of symbol.
    SymbolKind kind;

	/// The name of the symbol; if the symbol does not have a name,
	/// this will be an empty string.
    StringRef name;

	/// The declared location of the symbol in the source code, or an empty location
	/// if it was not explicitly declared in the source text. This is mainly used
	/// for reporting errors.
    SourceLocation location;

	/// The symbol that contains this symbol in the source text, or null if
	/// it is not contained by anything.
	const Symbol* containingSymbol;

	/// Finds the first ancestor symbol of the given kind. If this symbol is already of
	/// the given kind, returns this symbol.
	const Symbol* findAncestor(SymbolKind kind) const;

	/// Get the symbol for the root of the design.
	const DesignRootSymbol& getRoot() const;

	template<typename T>
	const T& as() const { return *static_cast<const T*>(this); }

protected:
    explicit Symbol(SymbolKind kind, StringRef name = nullptr, SourceLocation location = SourceLocation(), const Symbol* containingSymbol = nullptr) :
        kind(kind), name(name), location(location),
		containingSymbol(containingSymbol) {}

	Symbol(SymbolKind kind, Token token, const Symbol* containingSymbol = nullptr) :
		kind(kind), name(token.valueText()), location(token.location()),
		containingSymbol(containingSymbol) {}

	Diagnostic& addError(DiagCode code, SourceLocation location) const;

	template<typename T, typename... Args>
	T& allocate(Args&&... args) const {
		return getRoot().allocate<T>(std::forward<Args>(args)...);
	}
};

/// Base class for symbols that also act as scopes, which means they contain
/// child symbols that can be looked up by name.
class ScopeSymbol : public Symbol {
public:
	/// Look up a symbol in the current scope. Returns null if no symbol is found.
	virtual const Symbol* lookup(StringRef name) const = 0;

	/// Look up a symbol in the current scope, expecting it to exist and be of the
	/// given type. If those conditions do not hold, this will assert.
	template<typename T>
	const T& lookup(StringRef name) const {
		const Symbol* sym = lookup(name);
		ASSERT(sym);
		return sym->as<T>();
	}

	/// A helper method to evaluate a constant in the current scope.
	ConstantValue evaluateConstant(const ExpressionSyntax& expr) const;

	/// A helper method to evaluate a constant in the current scope and then
	/// convert it to the given destination type. If the conversion fails, the
	/// returned value will be marked bad.
	ConstantValue evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType) const;

	/// A helper method to get a type symbol, using the current scope as context.
	const TypeSymbol& getType(const DataTypeSyntax& syntax) const;

protected:
	using Symbol::Symbol;
};

/// Base class for all data types.
class TypeSymbol : public Symbol {
public:
    // SystemVerilog defines various levels of type compatibility, which are used
    // in different scenarios. See the spec, section 6.22.
    bool isMatching(const TypeSymbol& rhs) const;
    bool isEquivalent(const TypeSymbol& rhs) const;
    bool isAssignmentCompatible(const TypeSymbol& rhs) const;
    bool isCastCompatible(const TypeSymbol& rhs) const;

    // Helpers to get the following pieces of information for any type symbol,
    // though the information is stored differently for different types
    bool isSigned() const;
    bool isReal() const;
    bool isFourState() const;
    int width() const;

    std::string toString() const;

protected:
	using Symbol::Symbol;
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    // a negative lower bound is actually an upper bound specified in the opposite order
    ArrayRef<int> lowerBounds;
    ArrayRef<int> widths;
    int width;
    TokenKind keywordType;
    bool isSigned;
    bool isFourState;

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState) :
        IntegralTypeSymbol(keywordType, width, isSigned, isFourState, EmptyLowerBound, ArrayRef<int>(&width, 1)) {}

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState, ArrayRef<int> lowerBounds, ArrayRef<int> widths) :
        TypeSymbol(SymbolKind::IntegralType, getTokenKindText(keywordType), SourceLocation()),
        lowerBounds(lowerBounds), widths(widths),
        width(width), keywordType(keywordType), isSigned(isSigned), isFourState(isFourState) {}

  private:
    static ArrayRef<int> EmptyLowerBound;
};

class RealTypeSymbol : public TypeSymbol {
public:
    int width;
    TokenKind keywordType;

    RealTypeSymbol(TokenKind keywordType, int width) :
        TypeSymbol(SymbolKind::RealType, getTokenKindText(keywordType), SourceLocation()),
        width(width), keywordType(keywordType) {}
};

//class EnumValueSymbol : public ConstValueSymbol {
//public:
//    EnumValueSymbol(StringRef name, SourceLocation location, const TypeSymbol *type, ConstantValue val) :
//        ConstValueSymbol(SymbolKind::EnumValue, name, location, type, val) {}
//};
//
//class EnumTypeSymbol : public TypeSymbol {
//public:
//    const IntegralTypeSymbol* baseType;
//    ArrayRef<EnumValueSymbol *> values;
//
//    EnumTypeSymbol(const IntegralTypeSymbol *baseType, SourceLocation location, ArrayRef<EnumValueSymbol *> values) :
//        TypeSymbol(SymbolKind::EnumType, "", location),
//        baseType(baseType), values(values) {}
//};

class StructTypeSymbol : public TypeSymbol {
public:
    bool isPacked;
    bool isSigned;
};

class ErrorTypeSymbol : public TypeSymbol {
public:
    ErrorTypeSymbol() : TypeSymbol(SymbolKind::Unknown, nullptr, SourceLocation()) {}

	static const ErrorTypeSymbol Default;
};

class TypeAliasSymbol : public TypeSymbol {
public:
    const SyntaxNode& syntax;
    const TypeSymbol* underlying;

    TypeAliasSymbol(const SyntaxNode& syntax, SourceLocation location, const TypeSymbol* underlying, StringRef alias) :
        TypeSymbol(SymbolKind::TypeAlias, alias, location),
        syntax(syntax), underlying(underlying) {}
};

class CompilationUnitSymbol;
class PackageSymbol;
class ParameterizedModuleSymbol;
class ModuleInstanceSymbol;

/// Represents the entirety of a design, along with all contained compilation units.
class DesignRootSymbol : public ScopeSymbol {
public:
	static DesignRootSymbol& create(const SyntaxTree& tree);
	static DesignRootSymbol& create(BumpAllocator& alloc, Diagnostics& diagnostics, ArrayRef<const SyntaxTree*> syntaxTrees = nullptr);

	/// Adds a syntax tree to the design.
	void addTree(const SyntaxTree& tree);

	/// Gets all of the compilation units in the design.
	ArrayRef<const CompilationUnitSymbol*> units() const;

	/// Gets all of the top-level module instances in the design.
	/// These form the roots of the actual design hierarchy.
	ArrayRef<const ModuleInstanceSymbol*> tops() const;

	/// Finds a package in the design with the given name, or returns null if none is found.
	const PackageSymbol* findPackage(StringRef name) const;

	/// Finds a module, interface, or program with the given name, or returns null if none is found.
	const Symbol* findDefinition(StringRef name) const;

	/// Methods for getting various type symbols.
	const TypeSymbol& getType(const DataTypeSyntax& syntax, const ScopeSymbol& scope);
	const TypeSymbol& getKnownType(SyntaxKind kind) const;
	const TypeSymbol& getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false) const;

	/// Performs a look up for a symbol in the root scope.
	const Symbol* lookup(StringRef name) const final;

	/// Report an error at the specified location.
	Diagnostic& addError(DiagCode code, SourceLocation location) const {
		return diagnostics.add(code, location);
	}

	/// Allocate an object using the design's shared bump allocator.
	template<typename T, typename... Args>
	T& allocate(Args&&... args) const {
		return *alloc.emplace<T>(std::forward<Args>(args)...);
	}

	BumpAllocator& allocator() const { return alloc; }

private:
	DesignRootSymbol(BumpAllocator& alloc, Diagnostics& diagnostics, ArrayRef<const SyntaxTree*> syntaxTrees);

	BumpAllocator& alloc;
	Diagnostics& diagnostics;
};

/// The root of a single compilation unit. 
class CompilationUnitSymbol : public ScopeSymbol {
public:
	CompilationUnitSymbol(const CompilationUnitSyntax& syntax);

	SymbolList members() const;

	const Symbol* lookup(StringRef name) const final;
};

/// A SystemVerilog package construct.
class PackageSymbol : public ScopeSymbol {
public:
	PackageSymbol(const ModuleDeclarationSyntax& package, const Symbol& parent);

	SymbolList members() const;

	const Symbol* lookup(StringRef name) const final;
};

/// Represents a module declaration, with its parameters still unresolved.
class ModuleSymbol : public Symbol {
public:
	ModuleSymbol(const ModuleDeclarationSyntax& decl, const Symbol& container);

	/// Parameterizes the module with the given set of parameter assignments.
	const ParameterizedModuleSymbol& parameterize(const ParameterValueAssignmentSyntax* assignments = nullptr,
												  const ScopeSymbol* instanceScope = nullptr) const;

private:
	// Small collection of info extracted from a parameter definition
	struct ParameterInfo {
		const ParameterDeclarationSyntax& paramDecl;
		const VariableDeclaratorSyntax& declarator;
		StringRef name;
		SourceLocation location;
		ExpressionSyntax* initializer;
		bool local;
		bool bodyParam;
	};

	const std::vector<ParameterInfo>& getDeclaredParams() const;
	ConstantValue evaluate(const ParameterDeclarationSyntax& paramDecl, const ScopeSymbol& scope, const ExpressionSyntax& expr) const;

	// Helper function used by getModuleParams to convert a single parameter declaration into
	// one or more ParameterInfo instances.
	bool getParamDecls(const ParameterDeclarationSyntax& syntax, std::vector<ParameterInfo>& buffer,
	                   HashMapBase<StringRef, SourceLocation>& nameDupMap,
	                   bool lastLocal, bool overrideLocal, bool bodyParam) const;

	const ModuleDeclarationSyntax& decl;
	mutable std::optional<std::vector<ParameterInfo>> paramInfoCache;
};

/// Represents a module that has had its parameters resolved to a specific set of values.
class ParameterizedModuleSymbol : public ScopeSymbol {
public:
	ParameterizedModuleSymbol(const ModuleSymbol& module, const HashMapBase<StringRef, ConstantValue>& parameterAssignments);

	SymbolList members() const;
	
	template<typename T>
	const T& member(uint32_t index) const { return members()[index]->as<T>(); }

	const Symbol* lookup(StringRef name) const final;

private:
	const ModuleSymbol& module;
};

class ModuleInstanceSymbol : public Symbol {
public:
	ParameterizedModuleSymbol& module;

	/// A helper method to access a specific member of the module (of which this is an instance).
	template<typename T>
	const T& member(uint32_t index) const { return members()[index]->as<T>(); }
};

class GenvarSymbol : public Symbol {
public:
    GenvarSymbol(StringRef name, SourceLocation location) :
        Symbol(SymbolKind::Genvar, name, location) {}
};

class VariableSymbol : public Symbol {
public:
    class Modifiers {
    public:
        unsigned int constM : 1;
        unsigned int varM : 1;
        unsigned int staticM : 1;
        unsigned int automaticM : 1;
    };

    Modifiers modifiers;
    const TypeSymbol* type;
    const BoundExpression* initializer;

    VariableSymbol(Token name, const TypeSymbol* type, const BoundExpression* initializer = nullptr,
                   Modifiers modifiers = Modifiers()) :
        Symbol(SymbolKind::Variable, name.valueText(), name.location()),
        modifiers(modifiers),
        type(type),
        initializer(initializer) {}

    VariableSymbol(StringRef name, SourceLocation location, const TypeSymbol* type,
                   const BoundExpression* initializer = nullptr, Modifiers modifiers = Modifiers()) :
        Symbol(SymbolKind::Variable, name, location),
        modifiers(modifiers),
        type(type),
        initializer(initializer) {}

protected:
    VariableSymbol(SymbolKind childKind, StringRef name, SourceLocation location,
                   const TypeSymbol* type, const BoundExpression* initializer) :
        Symbol(childKind, name, location), type(type), initializer(initializer) {}
};

//class GenerateBlock : public Symbol {
//public:
//    ArrayRef<const Symbol*> children;
//    const Scope *scope;
//
//    GenerateBlock(ArrayRef<const Symbol*> children, const Scope *scope) :
//        children(children), scope(scope) {}
//
//    template<typename T>
//    const T& getChild(uint32_t index) const { return children[index]->as<T>(); }
//
//    static constexpr SymbolKind mykind = SymbolKind::GenerateBlock;
//};

//class ProceduralBlock : public Symbol {
//public:
//    ArrayRef<const Symbol *> children;
//    enum Kind {
//        Initial,
//        Final,
//        Always,
//        AlwaysComb,
//        AlwaysFF,
//        AlwaysLatch
//    } kind;
//    const Scope *scope;
//
//    ProceduralBlock(ArrayRef<const Symbol*> children, Kind kind, const Scope *scope)
//        : children(children), kind(kind), scope(scope) {}
//};

class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol(Token name, const TypeSymbol* type, const BoundExpression* initializer, FormalArgumentDirection direction) :
        VariableSymbol(SymbolKind::FormalArgument, name.valueText(), name.location(), type, initializer),
        direction(direction) {}

    FormalArgumentSymbol(const TypeSymbol* type) :
        VariableSymbol(SymbolKind::FormalArgument, nullptr, SourceLocation(), type, nullptr) {}
};

class SubroutineSymbol : public Symbol {
public:
    const TypeSymbol* returnType;
    const BoundStatementList* body;
    ArrayRef<const FormalArgumentSymbol*> arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunction = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(Token name, const TypeSymbol* returnType, ArrayRef<const FormalArgumentSymbol*> arguments,
                     VariableLifetime defaultLifetime, bool isTask) :
        Symbol(SymbolKind::Subroutine, name.valueText(), name.location()),
        returnType(returnType), arguments(arguments),
        defaultLifetime(defaultLifetime), isTask(isTask) {}

    SubroutineSymbol(StringRef name, const TypeSymbol* returnType, ArrayRef<const FormalArgumentSymbol*> arguments,
                     SystemFunction systemFunction) :
        Symbol(SymbolKind::Subroutine, name, SourceLocation()),
        returnType(returnType), arguments(arguments), systemFunction(systemFunction) {}
};

}
