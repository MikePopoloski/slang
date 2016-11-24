#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "SourceLocation.h"
#include "StringRef.h"

namespace slang {

using ConstantValue = std::variant<SVInt, double>;

enum class SymbolKind {
    Unknown,
    IntegralType,
    RealType,
    StringType,
    CHandleType,
    VoidType,
    EventType,
    Parameter,
    Instance
};

class Symbol {
public:
    SymbolKind kind;

    Symbol(SymbolKind kind) : kind(kind) {}

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }

    virtual SourceLocation location() const { return SourceLocation(); }
    virtual StringRef name() const { return nullptr; }
};

/// Base class for all data types
class TypeSymbol : public Symbol {
public:
    TypeSymbol(SymbolKind kind) : Symbol(kind) {}

    std::string toString() const;
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    ArrayRef<int> lowerBounds;
    ArrayRef<int> widths;
    int width;
    TokenKind keywordType;
    bool isSigned;
    bool isFourState;

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState) :
        IntegralTypeSymbol(keywordType, width, isSigned, isFourState, EmptyLowerBound, ArrayRef<int>(&width, 1)) {}

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState, ArrayRef<int> lowerBounds, ArrayRef<int> widths) :
        TypeSymbol(SymbolKind::IntegralType),
        width(width), keywordType(keywordType), isSigned(isSigned), isFourState(isFourState),
        lowerBounds(lowerBounds), widths(widths) {}

private:
    static ArrayRef<int> EmptyLowerBound;
};

class RealTypeSymbol : public TypeSymbol {
public:
    int width;
    TokenKind keywordType;

    RealTypeSymbol(TokenKind keywordType, int width) :
        TypeSymbol(SymbolKind::RealType),
        width(width), keywordType(keywordType) {}
};

class EnumTypeSymbol : public TypeSymbol {
public:
    TypeSymbol* baseType;
};

class StructTypeSymbol : public TypeSymbol {
public:
    bool isPacked;
    bool isSigned;
};

class ErrorTypeSymbol : public TypeSymbol {
public:
    ErrorTypeSymbol() :
        TypeSymbol(SymbolKind::Unknown) {}
};

class ParameterSymbol : public Symbol {
public:
    const ParameterDeclarationSyntax* syntax;
    const ExpressionSyntax* initializer;
    const TypeSymbol* type = nullptr;
    ConstantValue value;
    bool isLocal;

    // TODO: decide what we're doing here
    StringRef _name;
    SourceLocation _location;

    ParameterSymbol(StringRef name, SourceLocation location,
        const ParameterDeclarationSyntax* syntax,
        const ExpressionSyntax* initializer, bool isLocal);

    StringRef name() const override { return _name; }
    SourceLocation location() const override { return _location; }
};

class InstanceSymbol : public Symbol {
public:
    ArrayRef<ParameterSymbol*> portParameters;
    ArrayRef<ParameterSymbol*> bodyParameters;

    InstanceSymbol(ArrayRef<ParameterSymbol*> portParameters, ArrayRef<ParameterSymbol*> bodyParameters) :
        Symbol(SymbolKind::Instance),
        portParameters(portParameters), bodyParameters(bodyParameters) {}
};

}