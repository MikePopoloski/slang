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
    TypeAlias,
    Parameter,
    Module,
    Interface,
    Program,
    Attribute
};

class Symbol {
public:
    SymbolKind kind;
    StringRef name;
    SourceLocation location;

    Symbol() {}
    Symbol(SymbolKind kind, StringRef name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }
};

/// Base class for all data types
class TypeSymbol : public Symbol {
public:
    TypeSymbol(SymbolKind kind, StringRef name, SourceLocation location) :
        Symbol(kind, name, location) {}

    // SystemVerilog defines various level of type compatibility, which are used
    // in various scenarios. See the spec, section 6.22.
    bool isMatching(const TypeSymbol* rhs) const;
    bool isEquivalent(const TypeSymbol* rhs) const;
    bool isAssignmentCompatible(const TypeSymbol* rhs) const;
    bool isCastCompatible(const TypeSymbol* rhs) const;

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
        TypeSymbol(SymbolKind::IntegralType, getTokenKindText(keywordType), SourceLocation()),
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
        TypeSymbol(SymbolKind::RealType, getTokenKindText(keywordType), SourceLocation()),
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
        TypeSymbol(SymbolKind::Unknown, nullptr, SourceLocation()) {}
};

class TypeAliasSymbol : public TypeSymbol {
public:
    const SyntaxNode* syntax;
    const TypeSymbol* underlying;

    TypeAliasSymbol(const SyntaxNode* syntax, SourceLocation location, const TypeSymbol* underlying, StringRef alias) :
        TypeSymbol(SymbolKind::TypeAlias, alias, location),
        syntax(syntax), underlying(underlying) {}
};

class AttributeSymbol : public Symbol {
public:
    const AttributeSpecSyntax* syntax;
    const TypeSymbol* type;
    ConstantValue value;

    AttributeSymbol(const AttributeSpecSyntax* syntax, const TypeSymbol* type, ConstantValue value);
};

class ParameterSymbol : public Symbol {
public:
    const ParameterDeclarationSyntax* syntax;
    const TypeSymbol* type;
    ConstantValue value;
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location,
                    const ParameterDeclarationSyntax* syntax,
                    bool isLocal);
};

class ModuleSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax* syntax;
    ArrayRef<const ParameterSymbol*> parameters;

    ModuleSymbol(const ModuleDeclarationSyntax* syntax, ArrayRef<const ParameterSymbol*> parameters) :
        syntax(syntax), parameters(parameters) {}
};

class InstanceSymbol : public Symbol {
public:
    const ModuleSymbol* module;
    bool implicit;

    InstanceSymbol(const ModuleSymbol* module, bool implicit) :
        module(module), implicit(implicit) {}
};

}