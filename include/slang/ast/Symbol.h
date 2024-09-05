//------------------------------------------------------------------------------
//! @file Symbol.h
//! @brief Base class for all elaborated symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Lookup.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang::ast {

class DeclaredType;
class DefinitionSymbol;
class Scope;
enum class RandMode;

// clang-format off
#define SYMBOLKIND(x) \
    x(Unknown) \
    x(Root) \
    x(Definition) \
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
    x(DPIOpenArrayType) \
    x(AssociativeArrayType) \
    x(QueueType) \
    x(PackedStructType) \
    x(UnpackedStructType) \
    x(PackedUnionType) \
    x(UnpackedUnionType) \
    x(ClassType) \
    x(CovergroupType) \
    x(VoidType) \
    x(NullType) \
    x(CHandleType) \
    x(StringType) \
    x(EventType) \
    x(UnboundedType) \
    x(TypeRefType) \
    x(UntypedType) \
    x(SequenceType) \
    x(PropertyType) \
    x(VirtualInterfaceType) \
    x(TypeAlias) \
    x(ErrorType) \
    x(ForwardingTypedef) \
    x(NetType) \
    x(Parameter) \
    x(TypeParameter) \
    x(Port) \
    x(MultiPort) \
    x(InterfacePort) \
    x(Modport) \
    x(ModportPort) \
    x(ModportClocking) \
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
    x(ElabSystemTask) \
    x(GenericClassDef) \
    x(MethodPrototype) \
    x(UninstantiatedDef) \
    x(Iterator) \
    x(PatternVar) \
    x(ConstraintBlock) \
    x(DefParam) \
    x(Specparam) \
    x(Primitive) \
    x(PrimitivePort) \
    x(PrimitiveInstance) \
    x(SpecifyBlock) \
    x(Sequence) \
    x(Property) \
    x(AssertionPort) \
    x(ClockingBlock) \
    x(ClockVar) \
    x(LocalAssertionVar) \
    x(LetDecl) \
    x(Checker) \
    x(CheckerInstance) \
    x(CheckerInstanceBody) \
    x(RandSeqProduction) \
    x(CovergroupBody) \
    x(Coverpoint) \
    x(CoverCross) \
    x(CoverCrossBody) \
    x(CoverageBin) \
    x(TimingPath) \
    x(PulseStyle) \
    x(SystemTimingCheck) \
    x(AnonymousProgram) \
    x(NetAlias) \
    x(ConfigBlock)
// clang-format on

SLANG_ENUM(SymbolKind, SYMBOLKIND)
#undef SYMBOLKIND

/// A numeric index that can be used to compare the relative ordering of symbols
/// within a single lexical scope.
enum class SLANG_EXPORT SymbolIndex : uint32_t {};

/// Base class for all symbols (logical code constructs) such as modules, types,
/// functions, variables, etc.
class SLANG_EXPORT Symbol {
public:
    /// The type of symbol.
    SymbolKind kind;

    /// The name of the symbol; if the symbol does not have a name,
    /// this will be an empty string.
    std::string_view name;

    /// The declared location of the symbol in the source code, or an empty location
    /// if it was not explicitly declared in the source text.
    SourceLocation location;

    Symbol(const Symbol&) = delete;
    Symbol& operator=(const Symbol&) = delete;

    /// Gets the logical parent scope that contains this symbol.
    const Scope* getParentScope() const { return parentScope; }

    /// Gets the parent scope of this symbol in terms of its hierarchy location.
    /// This is the same as getParentScope except for instance body symbols.
    const Scope* getHierarchicalParent() const;

    /// Gets the syntax node that was used to create this symbol, if any. Symbols can
    /// be created without any originating syntax; in those cases, this returns nullptr.
    const syntax::SyntaxNode* getSyntax() const { return originatingSyntax; }

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
    std::optional<bool> isDeclaredBefore(const Symbol& symbol) const;
    std::optional<bool> isDeclaredBefore(LookupLocation location) const;

    /// Gets the definition in which this symbol is declared. If the symbol isn't
    /// declared in a definition, returns nullptr.
    const DefinitionSymbol* getDeclaringDefinition() const;

    /// Gets the source library that contains this symbol.
    const SourceLibrary* getSourceLibrary() const;

    /// If this symbol is a random variable, returns its mode.
    /// Otherwise returns RandMode::None.
    RandMode getRandMode() const;

    /// Sets the attributes associated with this symbol.
    void setAttributes(const Scope& scope,
                       std::span<const syntax::AttributeInstanceSyntax* const> syntax);

    /// @brief Casts this symbol to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this symbol's kind.
    template<typename T>
    decltype(auto) as() {
        if constexpr (std::is_same_v<T, Scope>) {
            const Scope* scope = scopeOrNull();
            SLANG_ASSERT(scope);
            return *scope;
        }
        else {
            SLANG_ASSERT(T::isKind(kind));
            return *static_cast<T*>(this);
        }
    }

    /// @brief Tries to cast this symbol to the given concrete derived type.
    ///
    /// If the type is not appropriate given this symbol's kind, returns nullptr.
    template<typename T>
    decltype(auto) as_if() {
        if constexpr (std::is_same_v<T, Scope>) {
            return scopeOrNull();
        }
        else {
            if (!T::isKind(kind))
                return static_cast<T*>(nullptr);
            return static_cast<T*>(this);
        }
    }

    /// @brief Casts this symbol to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this symbol's kind.
    template<typename T>
    const T& as() const {
        return const_cast<Symbol*>(this)->as<T>();
    }

    /// @brief Tries to cast this symbol to the given concrete derived type.
    ///
    /// If the type is not appropriate given this symbol's kind, returns nullptr.
    template<typename T>
    const T* as_if() const {
        return const_cast<Symbol*>(this)->as_if<T>();
    }

    /// Gets the index of the symbol within its parent scope, which can be used
    /// to determine the relative ordering of scope members.
    SymbolIndex getIndex() const { return indexInScope; }

    /// Sets the index of this symbol within its parent scope.
    void setIndex(SymbolIndex index) { indexInScope = index; }

    /// Sets the syntax that was used to create this symbol.
    void setSyntax(const syntax::SyntaxNode& node) { originatingSyntax = &node; }

    /// Returns the next sibling symbol in the parent scope, if one exists.
    const Symbol* getNextSibling() const { return nextInScope; }

    /// Sets the parent scope of this symbol.
    ///
    /// Typically this is not called directly; add the symbol to the scope
    /// via the Scope::addMember method.
    void setParent(const Scope& scope) { parentScope = &scope; }

    /// Sets the parent scope of this symbol.
    ///
    /// Typically this is not called directly; add the symbol to the scope
    /// via the Scope::addMember method.
    void setParent(const Scope& scope, SymbolIndex index) {
        setParent(scope);
        indexInScope = index;
    }

    /// Visits this symbol's concrete derived type via the provided visitor object.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Symbol(SymbolKind kind, std::string_view name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

private:
    friend class Scope;

    const Scope* scopeOrNull() const;

    // When a symbol is first added to a scope a pointer to it will be stored here.
    // Along with that pointer, a linked list of members in the scope will be created
    // by using the nextInScope pointer, and the index within the scope (used to quickly
    // determine ordering during lookups) will be set here.
    mutable const Scope* parentScope = nullptr;
    mutable const Symbol* nextInScope = nullptr;
    mutable SymbolIndex indexInScope{0};

    const syntax::SyntaxNode* originatingSyntax = nullptr;
};

inline SymbolIndex operator+(SymbolIndex si, uint32_t offset) {
    return SymbolIndex(uint32_t(si) + offset);
}

inline SymbolIndex& operator+=(SymbolIndex& si, uint32_t offset) {
    si = si + offset;
    return si;
}

inline SymbolIndex operator-(SymbolIndex si, uint32_t offset) {
    return SymbolIndex(uint32_t(si) - offset);
}

inline SymbolIndex& operator-=(SymbolIndex& si, uint32_t offset) {
    si = si - offset;
    return si;
}

} // namespace slang::ast
