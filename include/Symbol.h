#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
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
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location, bool isLocal) :
        Symbol(name, location), isLocal(isLocal) {}
};

/// Symbol for design elements, which includes things like modules, interfaces, programs, etc.
class DesignElementSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax* syntax;
    ArrayRef<ParameterSymbol*> parameters;
    bool isReferenced;
    
    DesignElementSymbol(const ModuleDeclarationSyntax* syntax, ArrayRef<ParameterSymbol*> parameters) :
        Symbol(syntax->header->name.valueText(), syntax->header->name.location()),
        syntax(syntax), parameters(parameters)
    {
    }
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