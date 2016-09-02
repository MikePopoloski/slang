#pragma once

#include "ArrayRef.h"

namespace slang {

class Symbol {
};

/// Base class for all data types
class TypeSymbol : public Symbol {
public:
    bool isAggregate() const;
    bool isSingular() const;
    bool isIntegral() const;
    bool isSimpleBitVector() const;
    bool isReal() const;
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    IntegralTypeSymbol(bool isSigned, int width);

    bool isSigned() const;
    int width() const;
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