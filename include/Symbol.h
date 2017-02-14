#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "ConstantValue.h"
#include "SourceLocation.h"
#include "StringRef.h"
#include "Scope.h"

namespace slang {

class BoundExpression;
class BoundStatement;
class BoundStatementList;

enum class SymbolKind {
    Unknown,
    IntegralType,
    RealType,
    StringType,
    CHandleType,
    VoidType,
    EventType,
    EnumType,
    TypeAlias,
    Parameter,
    EnumValue,
    Module,
    Interface,
    Program,
    Attribute,
    Genvar,
    GenerateBlock,
    ProceduralBlock,
    Variable,
    Instance,
    FormalArgument,
    Subroutine
};

/// Specifies the storage lifetime of a variable.
enum class VariableLifetime {
    Automatic,
    Static
};

/// Specifies behavior of an argument passed to a subroutine.
enum class FormalArgumentDirection {
    In,
    Out,
    InOut,
    Ref,
    ConstRef
};

/// Indicates which built-in system function is represented by a symbol.
enum class SystemFunction {
    Unknown,
    clog2
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

    // Helpers to get the following pieces of information for any type symbol,
    // though the information is stored differently for different types
    bool isSigned() const;
    bool isReal() const;
    bool isFourState() const;
    int width() const;

    std::string toString() const;
    static constexpr SymbolKind mykind = SymbolKind::Unknown;
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    // a negative lower bound is actually an upper bound specified in the opposite order
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

class ConstValueSymbol : public Symbol {
public:
    const TypeSymbol* type;
    ConstantValue value;

    ConstValueSymbol(SymbolKind kind, StringRef name, SourceLocation location) :
        Symbol(kind, name, location),
        // FIXME: fill this in with something meaningful
        // this is to prevent it from being uninitialized memory
        type(new TypeSymbol(SymbolKind::Unknown,"Unknown",location)) {}

    ConstValueSymbol(SymbolKind kind, StringRef name, SourceLocation location,
            const TypeSymbol * type, ConstantValue val) :
        Symbol(kind, name, location), type(type), value(val) {}
};

class EnumValueSymbol : public ConstValueSymbol {
public:
    EnumValueSymbol(StringRef name, SourceLocation location, const TypeSymbol *type, ConstantValue val) :
        ConstValueSymbol(SymbolKind::EnumValue, name, location, type, val) {}

    static constexpr SymbolKind mykind = SymbolKind::EnumValue;
};

class EnumTypeSymbol : public TypeSymbol {
public:
    const IntegralTypeSymbol* baseType;
    ArrayRef<EnumValueSymbol *> values;

    EnumTypeSymbol(const IntegralTypeSymbol *baseType, SourceLocation location, ArrayRef<EnumValueSymbol *> values) :
        TypeSymbol(SymbolKind::EnumType, "", location),
        baseType(baseType), values(values) {}
    static constexpr SymbolKind mykind = SymbolKind::EnumType;
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

class ParameterSymbol : public ConstValueSymbol {
public:
    const ParameterDeclarationSyntax* syntax;
    bool isLocal;

    ParameterSymbol(StringRef name, SourceLocation location,
                    const ParameterDeclarationSyntax* syntax,
                    bool isLocal) :
        ConstValueSymbol(SymbolKind::Parameter, name, location),
        syntax(syntax),
        isLocal(isLocal) {}

    static constexpr SymbolKind mykind = SymbolKind::Parameter;
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

    InstanceSymbol(const ModuleSymbol* module, StringRef name, SourceLocation location, bool implicit) :
        Symbol(SymbolKind::Instance, name, location),
        module(module), implicit(implicit) {}

    template<typename T>
    const T& getChild(uint32_t index) const { return module->children[index]->as<T>(); }

    static constexpr SymbolKind mykind = SymbolKind::Instance;
};

class GenvarSymbol : public Symbol {
public:
    GenvarSymbol(StringRef name, SourceLocation location) :
        Symbol(SymbolKind::Genvar, name, location) {}
};

class VariableSymbol : public Symbol {
public:
    class Modifiers {
    public:
        unsigned int constM : 1;
        unsigned int varM : 1;
        unsigned int staticM : 1;
        unsigned int automaticM : 1;
    };

    Modifiers modifiers;
    const TypeSymbol* type;
    const BoundExpression* initializer;

    VariableSymbol(Token name, const TypeSymbol* type, const BoundExpression* initializer = nullptr,
                   Modifiers modifiers = Modifiers()) :
        Symbol(SymbolKind::Variable, name.valueText(), name.location()),
        modifiers(modifiers),
        type(type),
        initializer(initializer) {}

    VariableSymbol(StringRef name, SourceLocation location, const TypeSymbol* type,
                   const BoundExpression* initializer = nullptr, Modifiers modifiers = Modifiers()) :
        Symbol(SymbolKind::Variable, name, location),
        modifiers(modifiers),
        type(type),
        initializer(initializer) {}

protected:
    VariableSymbol(SymbolKind childKind, StringRef name, SourceLocation location,
                   const TypeSymbol* type, const BoundExpression* initializer) :
        Symbol(childKind, name, location), type(type), initializer(initializer) {}
};

class GenerateBlock : public Symbol {
public:
    ArrayRef<const Symbol*> children;
    const Scope *scope;

    GenerateBlock(ArrayRef<const Symbol*> children, const Scope *scope) :
        children(children), scope(scope) {}

    template<typename T>
    const T& getChild(uint32_t index) const { return children[index]->as<T>(); }

    static constexpr SymbolKind mykind = SymbolKind::GenerateBlock;
};

class ProceduralBlock : public Symbol {
public:
    ArrayRef<const Symbol *> children;
    enum Kind {
        Initial,
        Final,
        Always,
        AlwaysComb,
        AlwaysFF,
        AlwaysLatch
    } kind;
    const Scope *scope;

    ProceduralBlock(ArrayRef<const Symbol*> children, Kind kind, const Scope *scope)
        : children(children), kind(kind), scope(scope) {}
};

class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol(Token name, const TypeSymbol* type, const BoundExpression* initializer, FormalArgumentDirection direction) :
        VariableSymbol(SymbolKind::FormalArgument, name.valueText(), name.location(), type, initializer),
        direction(direction) {}

    FormalArgumentSymbol(const TypeSymbol* type) :
        VariableSymbol(SymbolKind::FormalArgument, nullptr, SourceLocation(), type, nullptr) {}
};

class SubroutineSymbol : public Symbol {
public:
    const Scope* scope = nullptr;
    const TypeSymbol* returnType;
    const BoundStatementList* body;
    ArrayRef<const FormalArgumentSymbol*> arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunction = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(Token name, const TypeSymbol* returnType, ArrayRef<const FormalArgumentSymbol*> arguments,
                     VariableLifetime defaultLifetime, bool isTask, const Scope* scope) :
        Symbol(SymbolKind::Subroutine, name.valueText(), name.location()),
        returnType(returnType), arguments(arguments), defaultLifetime(defaultLifetime),
        isTask(isTask), scope(scope) {}

    SubroutineSymbol(StringRef name, const TypeSymbol* returnType, ArrayRef<const FormalArgumentSymbol*> arguments,
                     SystemFunction systemFunction) :
        Symbol(SymbolKind::Subroutine, name, SourceLocation()),
        returnType(returnType), arguments(arguments), systemFunction(systemFunction) {}
};

}
