#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

using ConstantValue = std::variant<SVInt, double>;

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
    bool isReal : 1;

    TypeSymbol() {
        isAggregate = false;
        isSingular = true;
        isIntegral = false;
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

class RealTypeSymbol : public TypeSymbol {
public:
    int width;

    RealTypeSymbol(int width) :
        width(width)
    {
        isReal = true;
    }
};

class IntegerVectorTypeSymbol : public IntegralTypeSymbol {
public:
    // Lower bounds for dimensions, by position.
    ArrayRef<int> lowerBounds;

    // Sizes for dimensions, by position.
    ArrayRef<int> widths;

    IntegerVectorTypeSymbol(int width, bool isSigned, bool isFourState,
                            ArrayRef<int> lowerBounds, ArrayRef<int> widths) :
        IntegralTypeSymbol(width, isSigned, isFourState), lowerBounds(lowerBounds), widths(widths)
    {
    }
};

class EnumTypeSymbol : public TypeSymbol {
public:
    TypeSymbol* baseType;
};

class ErrorTypeSymbol : public TypeSymbol {
};

class ParameterSymbol : public Symbol {
public:
    const ParameterDeclarationSyntax* syntax;
    const ExpressionSyntax* initializer;
    const TypeSymbol* type = nullptr;
    ConstantValue value;
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location,
        const ParameterDeclarationSyntax* syntax,
        const ExpressionSyntax* initializer, bool isLocal);
};

class InstanceSymbol : public Symbol {
public:
    ArrayRef<ParameterSymbol*> portParameters;
    ArrayRef<ParameterSymbol*> bodyParameters;

    InstanceSymbol(ArrayRef<ParameterSymbol*> portParameters, ArrayRef<ParameterSymbol*> bodyParameters) :
        portParameters(portParameters), bodyParameters(bodyParameters)
    {
    }
};

}