//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/symbols/DeclaredType.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

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
    Definition,
    Parameter,
    Port,
    InterfacePort,
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
    Subroutine,
    ContinuousAssign
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

    /// Gets the syntax node that was used to create this symbol, if any. Symbols can
    /// be created without any originating syntax; in those cases, this returns nullptr.
    const SyntaxNode* getSyntax() const { return originatingSyntax; }

    /// Determines whether this symbol also represents a scope.
    bool isScope() const { return scopeOrNull(); }

    /// Determines whether this symbol represents a type.
    bool isType() const;

    /// Determines whether this symbol represents a value.
    bool isValue() const;

    /// Determines whether this symbol is a module, interface, or program instance.
    bool isInstance() const;

    /// If the symbol has a declared type, returns a pointer to it. Otherwise returns nullptr.
    const DeclaredType* getDeclaredType() const;

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

    /// Sets the syntax that was used to create this symbol. Mostly called by
    /// various factory functions.
    void setSyntax(const SyntaxNode& node) { originatingSyntax = &node; }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    Symbol(SymbolKind kind, string_view name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

    Symbol(const Symbol&) = delete;

    void setParent(const Scope& scope) { parentScope = &scope; }
    void setParent(const Scope& scope, Index index) {
        setParent(scope);
        indexInScope = index;
    }

private:
    friend class Scope;

    const Scope* scopeOrNull() const;

    // When a symbol is first added to a scope a pointer to it will be stored here.
    // Along with that pointer, a linked list of members in the scope will be created
    // by using the nextInScope pointer, and the index within the scope (used to quickly
    // determine ordering during lookups) will be set here.
    mutable const Scope* parentScope = nullptr;
    mutable const Symbol* nextInScope = nullptr;
    mutable Index indexInScope{ 0 };

    const SyntaxNode* originatingSyntax = nullptr;
};

/// A base class for symbols that represent a value (for example a variable or a parameter).
/// The common functionality is that they all have a type.
class ValueSymbol : public Symbol {
public:
    /// Gets the type of the value.
    const Type& getType() const { return declaredType.getType(); }

    /// Sets the type of the value.
    void setType(const Type& type) { declaredType.setType(type); }

    /// Gets access to the symbol's declared type.
    not_null<const DeclaredType*> getDeclaredType() const { return &declaredType; }

    /// Sets the symbol's declared type.
    void setDeclaredType(const DataTypeSyntax& newType) { declaredType.setTypeSyntax(newType); }
    void setDeclaredType(const DataTypeSyntax& newType,
                         const SyntaxList<VariableDimensionSyntax>& newDimensions) {
        declaredType.setTypeSyntax(newType);
        declaredType.setDimensionSyntax(newDimensions);
    }

    /// Gets the initializer for this value, if it has one.
    const Expression* getInitializer() const { return declaredType.getInitializer(); }

    /// Sets the initializer for this value.
    void setInitializer(const Expression& expr) { declaredType.setInitializer(expr); }

    /// Sets the expression tree used to initialize this value.
    void setInitializerSyntax(const ExpressionSyntax& syntax, SourceLocation initLocation) {
        declaredType.setInitializerSyntax(syntax, initLocation);
    }

    /// Initializes the value's dimension and initializer syntax from the given declarator.
    void setFromDeclarator(const VariableDeclaratorSyntax& decl) {
        declaredType.setFromDeclarator(decl);
    }

    /// Gets the value of the symbol if it is a compile time constant.
    const ConstantValue& getConstantValue() const { return declaredType.getConstantValue(); }

    static bool isKind(SymbolKind kind);

protected:
    ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    DeclaredType declaredType;
};

/// Serialization of arbitrary symbols to JSON.
void to_json(json& j, const Symbol& symbol);

} // namespace slang
