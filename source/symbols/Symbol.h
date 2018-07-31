//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "text/SourceLocation.h"
#include "util/Util.h"

namespace slang {

class Scope;
class Type;

enum class SymbolKind {
    Unknown,
    Root,
    CompilationUnit,
    DeferredMember,
    TransparentMember,
    PredefinedIntegerType,
    ScalarType,
    FloatingType,
    EnumType,
    EnumValue,
    PackedArrayType,
    UnpackedArrayType,
    PackedStructType,
    UnpackedStructType,
    PackedUnionType,
    UnpackedUnionType,
    ClassType,
    VoidType,
    NullType,
    CHandleType,
    StringType,
    EventType,
    TypeAlias,
    ErrorType,
    ForwardingTypedef,
    NetType,
    Parameter,
    Modport,
    ModuleInstance,
    InterfaceInstance,
    Package,
    ExplicitImport,
    WildcardImport,
    Program,
    Attribute,
    Genvar,
    GenerateBlock,
    GenerateBlockArray,
    ProceduralBlock,
    SequentialBlock,
    Net,
    Variable,
    FormalArgument,
    Field,
    Subroutine
};

/// Base class for all symbols (logical code constructs) such as modules, types,
/// functions, variables, etc.
class Symbol {
public:
    /// The type of symbol.
    SymbolKind kind;

    /// The name of the symbol; if the symbol does not have a name,
    /// this will be an empty string.
    string_view name;

    /// The declared location of the symbol in the source code, or an empty location
    /// if it was not explicitly declared in the source text. This is mainly used
    /// for reporting errors.
    SourceLocation location;

    /// Gets the lexical scope that contains this symbol.
    const Scope* getScope() const { return parentScope; }

    /// Finds the first ancestor symbol of the given kind. If this symbol is already of
    /// the given kind, returns this symbol.
    const Symbol* findAncestor(SymbolKind searchKind) const;

    /// Determines whether this symbol also represents a scope.
    bool isScope() const { return scopeOrNull(); }

    /// Determines whether this symbol represents a type.
    bool isType() const;

    /// Determines whether this symbol represents a value.
    bool isValue() const;

    /// Determines whether this symbol is a module, interface, or program instance.
    bool isInstance() const;

    template<typename T>
    decltype(auto) as() {
        if constexpr (std::is_same_v<T, Scope>) {
            const Scope* scope = scopeOrNull();
            ASSERT(scope);
            return *scope;
        }
        else {
            ASSERT(T::isKind(kind));
            return *static_cast<T*>(this);
        }
    }

    template<typename T>
    const T& as() const {
        return const_cast<Symbol*>(this)->as<T>();
    }

    /// A numeric index that can be used to compare the relative ordering of symbols
    /// within a single lexical scope.
    enum class Index : uint32_t {};

    /// Gets the index of the symbol within its parent scope, which can be used
    /// to determine the relative ordering of scope members.
    Index getIndex() const { return indexInScope; }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit Symbol(SymbolKind kind, string_view name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

    Symbol(const Symbol&) = delete;

    void setParent(const Scope& scope) { parentScope = &scope; }

private:
    friend class Scope;

    const Scope* scopeOrNull() const;

    // When a symbol is first added to a scope a pointer to it will be stored here.
    // Along with that pointer, a linked list of members in the scope will be created
    // by using the nextInScope pointer, and the index within the scope (used to quickly
    // determine ordering during lookups) will set here.
    mutable const Scope* parentScope = nullptr;
    mutable const Symbol* nextInScope = nullptr;
    mutable Index indexInScope {0};
};

/// A base class for symbols that represent a value (for example a variable or a parameter).
/// The common functionality is that they all have a type.
class ValueSymbol : public Symbol {
public:
    /// Gets the type of the value.
    const Type& getType() const;

    static bool isKind(SymbolKind kind);

protected:
    using Symbol::Symbol;
};

/// Serialization of arbitrary symbols to JSON.
void to_json(json& j, const Symbol& symbol);

}
