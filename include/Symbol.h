#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "BoundNodes.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

class IntegralTypeSymbol;

class Symbol {
public:
    StringRef name;
    SourceLocation location;

    Symbol() {}
    Symbol(StringRef name, SourceLocation location) :
        name(name), location(location)
    {
    }
};

class ParameterSymbol : public Symbol {
public:
	const DataTypeSyntax* typeSyntax;
	const ExpressionSyntax* initializer;
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location, const DataTypeSyntax* typeSyntax, const ExpressionSyntax* initializer, bool isLocal) :
        Symbol(name, location), typeSyntax(typeSyntax), initializer(initializer), isLocal(isLocal)
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

class ParameterInstance {
public:
	const ParameterSymbol* symbol;
	ConstantValue value;

	ParameterInstance(const ParameterSymbol* symbol, ConstantValue value) :
		symbol(symbol), value(value)
	{
	}
};

class InstanceSymbol : public Symbol {
public:
	ArrayRef<ParameterInstance> parameters;

	InstanceSymbol(ArrayRef<ParameterInstance> parameters) :
		parameters(parameters)
	{
	}
};

/// A SystemVerilog parameter (or localparam)
//class ParameterSymbol : public Symbol {
//public:
//    const ParameterDeclarationSyntax* syntax;
//    BoundExpression* initializer;
//    ConstantValue value;
//
//    ParameterSymbol(const ParameterDeclarationSyntax* syntax, BoundExpression* initializer) :
//        syntax(syntax), initializer(initializer), value(initializer->constantValue)
//    {
//    }
//};

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

}