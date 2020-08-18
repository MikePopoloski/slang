//------------------------------------------------------------------------------
//! @file Symbol.h
//! @brief Base class for all elaborated symbols
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/DeclaredType.h"
#include "slang/symbols/Lookup.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang {

class ASTSerializer;
class Compilation;
class Scope;
class Type;
struct AttributeInstanceSyntax;

// clang-format off
#define SYMBOLKIND(x) \
    x(Unknown) \
    x(Root) \
    x(CompilationUnit) \
    x(DeferredMember) \
    x(TransparentMember) \
    x(EmptyMember) \
    x(PredefinedIntegerType) \
    x(ScalarType) \
    x(FloatingType) \
    x(EnumType) \
    x(EnumValue) \
    x(PackedArrayType) \
    x(FixedSizeUnpackedArrayType) \
    x(DynamicArrayType) \
    x(AssociativeArrayType) \
    x(QueueType) \
    x(PackedStructType) \
    x(UnpackedStructType) \
    x(PackedUnionType) \
    x(UnpackedUnionType) \
    x(ClassType) \
    x(VoidType) \
    x(NullType) \
    x(CHandleType) \
    x(StringType) \
    x(EventType) \
    x(TypeAlias) \
    x(ErrorType) \
    x(ForwardingTypedef) \
    x(NetType) \
    x(Parameter) \
    x(TypeParameter) \
    x(Port) \
    x(InterfacePort) \
    x(Modport) \
    x(Instance) \
    x(InstanceBody) \
    x(InstanceArray) \
    x(Package) \
    x(ExplicitImport) \
    x(WildcardImport) \
    x(Attribute) \
    x(Genvar) \
    x(GenerateBlock) \
    x(GenerateBlockArray) \
    x(ProceduralBlock) \
    x(StatementBlock) \
    x(Net) \
    x(Variable) \
    x(FormalArgument) \
    x(Field) \
    x(ClassProperty) \
    x(Subroutine) \
    x(ContinuousAssign) \
    x(Gate) \
    x(GateArray)
// clang-format on

ENUM(SymbolKind, SYMBOLKIND)
#undef SYMBOLKIND

/// A numeric index that can be used to compare the relative ordering of symbols
/// within a single lexical scope.
enum class SymbolIndex : uint32_t {};

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

    /// Gets the logical parent scope that contains this symbol.
    const Scope* getParentScope() const { return parentScope; }

    /// Gets the syntax node that was used to create this symbol, if any. Symbols can
    /// be created without any originating syntax; in those cases, this returns nullptr.
    const SyntaxNode* getSyntax() const { return originatingSyntax; }

    /// Determines whether this symbol also represents a scope.
    bool isScope() const { return scopeOrNull(); }

    /// Determines whether this symbol represents a type.
    bool isType() const;

    /// Determines whether this symbol represents a value.
    bool isValue() const;

    /// If the symbol has a declared type, returns a pointer to it. Otherwise returns nullptr.
    const DeclaredType* getDeclaredType() const;

    /// Gets the symbol's hierarchical path by walking up to the root node and appending
    /// each parent's name.
    void getHierarchicalPath(std::string& buffer) const;

    /// Gets the symbol's lexical path by walking up to the compilation unit and appending
    /// each parent's name.
    void getLexicalPath(std::string& buffer) const;

    /// Determines whether this symbol is considered to be declared before the
    /// given symbol, in the same compilation unit. If it is, this method returns true.
    /// Otherwise it returns false. If the given symbol is not even in the same
    /// compilation unit as this one, returns std::nullopt.
    optional<bool> isDeclaredBefore(const Symbol& symbol) const;
    optional<bool> isDeclaredBefore(LookupLocation location) const;

    void setAttributes(const Scope& scope, span<const AttributeInstanceSyntax* const> syntax);

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

    /// Gets the index of the symbol within its parent scope, which can be used
    /// to determine the relative ordering of scope members.
    SymbolIndex getIndex() const { return indexInScope; }

    /// Sets the syntax that was used to create this symbol. Mostly called by
    /// various factory functions.
    void setSyntax(const SyntaxNode& node) { originatingSyntax = &node; }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Symbol(SymbolKind kind, string_view name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

    Symbol(const Symbol&) = delete;

    void setParent(const Scope& scope) { parentScope = &scope; }
    void setParent(const Scope& scope, SymbolIndex index) {
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
    mutable SymbolIndex indexInScope{ 0 };

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
    not_null<DeclaredType*> getDeclaredType() { return &declaredType; }

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
    void setFromDeclarator(const DeclaratorSyntax& decl);

    static bool isKind(SymbolKind kind);

protected:
    ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    DeclaredType declaredType;
};

} // namespace slang
