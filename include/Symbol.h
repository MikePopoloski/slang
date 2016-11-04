#pragma once

#include "ArrayRef.h"
#include "BoundNodes.h"

namespace slang {

class IntegralTypeSymbol;

class Symbol {
};

class ParameterSymbol : public Symbol {
public:
    StringRef name;
    bool isLocal;

    ParameterSymbol(StringRef name, bool isLocal) : name(name), isLocal(isLocal) {}
};

/// Symbol for design elements, which includes things like modules, interfaces, programs, etc.
class DesignElementSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax* syntax;
    StringRef name;
    ArrayRef<ParameterSymbol*> parameters;
    
    DesignElementSymbol(const ModuleDeclarationSyntax* syntax, StringRef name, ArrayRef<ParameterSymbol*> parameters) :
        syntax(syntax), name(name), parameters(parameters)
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