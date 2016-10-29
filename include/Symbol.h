#pragma once

#include "ArrayRef.h"

namespace slang {

class IntegralTypeSymbol;

class Symbol {
};

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