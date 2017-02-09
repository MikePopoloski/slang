#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "ConstantValue.h"
#include "SourceLocation.h"
#include "StringRef.h"
#include "Scope.h"

namespace slang {

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
    Attribute,
    Genvar,
    GenerateBlock,
    LocalVariable
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
    const T& as() const {
        // TODO: if (T::mykind != this->kind) return nullptr;
        return *static_cast<const T*>(this);
    }
    static constexpr SymbolKind mykind = SymbolKind::Unknown;
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
    static constexpr SymbolKind mykind = SymbolKind::Unknown;
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

    static constexpr SymbolKind mykind = SymbolKind::IntegralType;

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

    static constexpr SymbolKind mykind = SymbolKind::RealType;
};

class EnumTypeSymbol : public TypeSymbol {
public:
    TypeSymbol* baseType;

    static constexpr SymbolKind mykind = SymbolKind::Unknown;
};

class StructTypeSymbol : public TypeSymbol {
public:
    bool isPacked;
    bool isSigned;
    static constexpr SymbolKind mykind = SymbolKind::Unknown;
};

class ErrorTypeSymbol : public TypeSymbol {
public:
    ErrorTypeSymbol() :
        TypeSymbol(SymbolKind::Unknown, nullptr, SourceLocation()) {}

    static constexpr SymbolKind mykind = SymbolKind::Unknown;
};

class TypeAliasSymbol : public TypeSymbol {
public:
    const SyntaxNode* syntax;
    const TypeSymbol* underlying;

    TypeAliasSymbol(const SyntaxNode* syntax, SourceLocation location, const TypeSymbol* underlying, StringRef alias) :
        TypeSymbol(SymbolKind::TypeAlias, alias, location),
        syntax(syntax), underlying(underlying) {}

    static constexpr SymbolKind mykind = SymbolKind::TypeAlias;
};

class AttributeSymbol : public Symbol {
public:
    const AttributeSpecSyntax* syntax;
    const TypeSymbol* type;
    ConstantValue value;

    AttributeSymbol(const AttributeSpecSyntax* syntax, const TypeSymbol* type, ConstantValue value);

    static constexpr SymbolKind mykind = SymbolKind::Attribute;
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

    static constexpr SymbolKind mykind = SymbolKind::Parameter;
};

class LocalVariableSymbol : public Symbol {
public:
    const TypeSymbol* type;

    LocalVariableSymbol(Token token, const TypeSymbol* type) :
        LocalVariableSymbol(token.valueText(), token.location(), type) {}

    LocalVariableSymbol(StringRef name, SourceLocation location, const TypeSymbol* type) :
        Symbol(SymbolKind::LocalVariable, name, location), type(type) {}
};

class ModuleSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax* syntax;
    Scope* scope;
    ArrayRef<const Symbol*> children;

    ModuleSymbol(const ModuleDeclarationSyntax* syntax, Scope* scope,
                 ArrayRef<const Symbol*> children) :
        Symbol(SymbolKind::Module, syntax->header->name.valueText(), syntax->header->name.location()),
        syntax(syntax), scope(scope), children(children) {}

    static constexpr SymbolKind mykind = SymbolKind::Module;
};

class InstanceSymbol : public Symbol {
public:
    const ModuleSymbol* module;
    bool implicit;

    InstanceSymbol(const ModuleSymbol* module, bool implicit) :
        module(module), implicit(implicit) {}

    template<typename T>
    const T& getChild(uint32_t index) const { return module->children[index]->as<T>(); }

    static constexpr SymbolKind mykind = SymbolKind::Unknown;
};

class GenvarSymbol : public Symbol {
public:
    GenvarSymbol(StringRef name, SourceLocation location) :
        Symbol(SymbolKind::Genvar, name, location) {}
};

class GenerateBlock : public Symbol {
public:
    ArrayRef<const Symbol*> children;

    GenerateBlock(ArrayRef<const Symbol*> children) :
        children(children) {}

    template<typename T>
    const T& getChild(uint32_t index) const { return children[index]->as<T>(); }

    static constexpr SymbolKind mykind = SymbolKind::GenerateBlock;
};

}
