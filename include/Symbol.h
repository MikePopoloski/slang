#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

using ConstantValue = variant<SVInt, double>;

enum class SymbolKind {
	Unknown,
	Parameter
};

class Symbol {
public:
	SymbolKind kind;
    StringRef name;
    SourceLocation location;

    Symbol() {}
    Symbol(SymbolKind kind, StringRef name, SourceLocation location) :
        kind(kind), name(name), location(location)
    {
    }

	template<typename T>
	const T* as() const { return static_cast<const T*>(this); }
};

class IntegralTypeSymbol;

/// Base class for all data types
class TypeSymbol : public Symbol {
public:
	bool isAggregate : 1;
	bool isSingular : 1;
	bool isIntegral : 1;
	bool isSimpleBitVector : 1;
	bool isReal : 1;

	TypeSymbol() {
		isAggregate = false;
		isSingular = false;
		isIntegral = false;
		isSimpleBitVector = false;
		isReal = false;
	}

	const IntegralTypeSymbol& integral() const {
		ASSERT(isIntegral);
		return *(IntegralTypeSymbol*)this;
	}
};

class IntegralTypeSymbol : public TypeSymbol {
public:
	int width;
	bool isSigned : 1;
	bool isFourState : 1;

	IntegralTypeSymbol(int width, bool isSigned, bool isFourState) :
		width(width), isSigned(isSigned), isFourState(isFourState)
	{
		isIntegral = true;
	}
};

class IntegerVectorTypeSymbol : public IntegralTypeSymbol {
public:
	// Lower bounds for dimensions, by position.
	ArrayRef<int> lowerBounds;

	// Sizes for dimensions, by position.
	ArrayRef<int> sizes;
};

class EnumTypeSymbol : public TypeSymbol {
public:
	TypeSymbol* baseType;
};

class ErrorTypeSymbol : public TypeSymbol {
};

class ParameterSymbol : public Symbol {
public:
	const DataTypeSyntax* typeSyntax;
	const ExpressionSyntax* initializer;
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location, const DataTypeSyntax* typeSyntax, const ExpressionSyntax* initializer, bool isLocal) :
        Symbol(SymbolKind::Unknown, name, location), typeSyntax(typeSyntax), initializer(initializer), isLocal(isLocal)
	{
	}
};

/// Symbol for design elements, which includes things like modules, interfaces, programs, etc.
/// Note that this basically just ties together parameters, since we can't reliably know the types
/// of anything else, including ports, until we know each instance's parameter values.
class DesignElementSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax* syntax;
    ArrayRef<ParameterSymbol*> parameters;
    bool isReferenced = false;
    
	DesignElementSymbol(const ModuleDeclarationSyntax* syntax, ArrayRef<ParameterSymbol*> parameters);

	bool canImplicitlyInstantiate() const;
};

class CompilationUnitSymbol : public Symbol {
public:
	const CompilationUnitSyntax* syntax;
	ArrayRef<DesignElementSymbol*> elements;

	CompilationUnitSymbol(const CompilationUnitSyntax* syntax, ArrayRef<DesignElementSymbol*> elements) :
		syntax(syntax), elements(elements)
	{
	}
};

class ParameterInstanceSymbol : public Symbol {
public:
	const TypeSymbol* type = nullptr;
	ConstantValue value;

	ParameterInstanceSymbol(const ParameterSymbol* symbol) :
		Symbol(SymbolKind::Parameter, symbol->name, symbol->location)
	{
	}
};

class InstanceSymbol : public Symbol {
public:
	ArrayRef<ParameterInstanceSymbol*> parameters;

	InstanceSymbol(ArrayRef<ParameterInstanceSymbol*> parameters) :
		parameters(parameters)
	{
	}
};

}