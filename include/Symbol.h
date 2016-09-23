#pragma once

#include "ArrayRef.h"

namespace slang {

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
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    IntegralTypeSymbol(bool isSigned, int width) :
        isSigned(isSigned), width(width)
    {
    }

    bool isSigned : 1;
    int width : 1;
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

}