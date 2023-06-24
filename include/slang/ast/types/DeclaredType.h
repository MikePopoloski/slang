//------------------------------------------------------------------------------
//! @file DeclaredType.h
//! @brief Glue logic between symbols and their declared types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/syntax/SyntaxFwd.h"
#include "slang/syntax/SyntaxNode.h"

namespace slang::ast {

class ASTContext;
class Expression;
class Symbol;
class Type;
class ValueSymbol;

enum class SymbolIndex : uint32_t;

/// Various flags that control declared type resolution.
enum class SLANG_EXPORT DeclaredTypeFlags {
    /// No special flags specified.
    None = 0,

    /// If the declared type is implicit, the actual type should be
    /// inferred from the initializer. If this is not set, the type
    /// will be resolved as 'logic' if implicit syntax is provided.
    InferImplicit = 1 << 0,

    /// The initializer expression cannot refer to the parent symbol.
    /// This is used for parameters which would otherwise be infinitely
    /// recursive if they referenced themselves.
    InitializerCantSeeParent = 1 << 1,

    /// The initializer expression has been overridden via a parameter
    /// in a hierarchical instantation.
    InitializerOverridden = 1 << 2,

    /// The type has been overridden via a type parameter in a hierarchical
    /// instantation.
    TypeOverridden = 1 << 3,

    /// The initializer is for an automatic variable.
    AutomaticInitializer = 1 << 4,

    /// The declared type is the target of a typedef.
    TypedefTarget = 1 << 5,

    /// The declared type is a net type.
    NetType = 1 << 6,

    /// The declared type is a user-defined net type.
    UserDefinedNetType = 1 << 7,

    /// The declared type is part of a port I/O declaration
    /// and should be merged with the formal argument declared
    /// elsewhere in the scope.
    FormalArgMergeVar = 1 << 8,

    /// The declared type is for a random variable
    Rand = 1 << 9,

    /// The declared type is a DPI return type.
    DPIReturnType = 1 << 10,

    /// The declared type is for a DPI argument.
    DPIArg = 1 << 11,

    /// Allow use of the unbounded literal '$' in the initializer expression.
    AllowUnboundedLiteral = 1 << 12,

    /// The type must be one allowed in a sequence expression.
    RequireSequenceType = 1 << 13,

    /// The type must be valid in a coverage expression.
    CoverageType = 1 << 14,

    /// The type is for an interconnect net, which has special rules.
    InterconnectNet = 1 << 15,

    /// The type is for a variable declaration inside an interface.
    InterfaceVariable = 1 << 16,

    /// A mask of flags that indicate additional type rules are needed to
    /// be checked after the type itself is resolved.
    NeedsTypeCheck = NetType | UserDefinedNetType | FormalArgMergeVar | Rand | DPIReturnType |
                     DPIArg | RequireSequenceType | CoverageType | InterfaceVariable
};
SLANG_BITMASK(DeclaredTypeFlags, InterfaceVariable)

/// Ties together various syntax nodes that declare the type of some parent symbol
/// along with the logic necessary to resolve that type. Optionally includes an
/// initializer expression as well, which can be necessary when resolving types that
/// are implicitly inferred from the initializer.
class SLANG_EXPORT DeclaredType {
public:
    /// Constructs a new instance of the class.
    /// @param parent The parent symbol that owns the declared type.
    /// @param flags Optional additional flags that constrain type resolution.
    explicit DeclaredType(const Symbol& parent,
                          bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);
    DeclaredType(const DeclaredType&) = delete;

    /// Resolves and returns the actual type.
    const Type& getType() const;

    /// Manually sets the resolved type, overriding anything that may have been
    /// resolved previously.
    void setType(const Type& newType) { type = &newType; }

    /// Sets the source syntax for the type, which will later be used when
    /// resolution is requested.
    void setTypeSyntax(const syntax::DataTypeSyntax& newType) {
        SLANG_ASSERT(!type);
        typeOrLink.typeSyntax = &newType;
        hasLink = false;
    }

    /// Sets this declared type to link to the given type, taking on whatever
    /// type and initializer that target has.
    void setLink(const DeclaredType& target);

    /// Gets the type syntax that was previously set via @a setTypeSyntax -- if any.
    /// Otherwise returns nullptr.
    const syntax::DataTypeSyntax* getTypeSyntax() const {
        return hasLink ? nullptr : typeOrLink.typeSyntax;
    }

    /// Sets an additional set of dimensions that represent the unpacked portion of
    /// the type declaration.
    void setDimensionSyntax(
        const syntax::SyntaxList<syntax::VariableDimensionSyntax>& newDimensions);

    /// Gets any previously set unpacked dimensions.
    const syntax::SyntaxList<syntax::VariableDimensionSyntax>* getDimensionSyntax() const {
        return dimensions;
    }

    /// Resolves and returns the initializer expression, if present. Otherwise returns nullptr.
    const Expression* getInitializer() const;

    /// Manually sets the resolved initializer expression, overriding anything
    /// that may have been resolved previously.
    void setInitializer(const Expression& expr) { initializer = &expr; }

    /// Sets the syntax for the initializer expression, which will be later used
    /// when resolution is requested.
    /// @param syntax The initializer expression syntax.
    /// @param loc The source location to use when reporting diagnostics about the initializer.
    void setInitializerSyntax(const syntax::ExpressionSyntax& syntax, SourceLocation loc) {
        SLANG_ASSERT(!initializer);
        initializerSyntax = &syntax;
        initializerLocation = loc;
    }

    /// Gets the initializer syntax previously set by @a setInitializerSyntax
    const syntax::ExpressionSyntax* getInitializerSyntax() const { return initializerSyntax; }

    /// Gets the initializer location previously set by @a setInitializerSyntax
    SourceLocation getInitializerLocation() const { return initializerLocation; }

    /// Sets type and initializer information from the given declarator syntax.
    /// This is just convenient shorthand for invoking @a setTypeSyntax and
    /// @a setInitializerSyntax manually.
    void setFromDeclarator(const syntax::DeclaratorSyntax& decl);

    /// Returns true if this declared type is in the process of being resolved.
    /// This is used to detect cycles in the the type resolution process.
    bool isEvaluating() const { return evaluating; }

    /// Sets a separate, later position in the parent scope for creating the
    /// declared type and initializer. This is used for merged port symbols
    /// because their declared I/O location and symbol location may differ.
    void setOverrideIndex(SymbolIndex index) { overrideIndex = uint32_t(index); }

    /// Adds additional type resolution flags to constrain resolution behavior.
    /// This will clear any resolved type to force resolution again with the
    /// new flags set.
    void addFlags(bitmask<DeclaredTypeFlags> toAdd) {
        SLANG_ASSERT(!type && !initializer);
        flags |= toAdd;
    }

    /// Gets the flags associated with this declared type.
    bitmask<DeclaredTypeFlags> getFlags() const { return flags; }

    /// Perform a merge of implicit port information; this facilitates the non-ascii
    /// port system permitted by Verilog, where port I/O declarations are separate
    /// from the actual symbol declaration but may still carry some type info.
    void mergeImplicitPort(
        const syntax::ImplicitTypeSyntax& implicit, SourceLocation location,
        std::span<const syntax::VariableDimensionSyntax* const> unpackedDimensions);

    /// Resolves the initializer using the given AST context, which could
    /// differ from the AST context that is used for type resolution.
    void resolveAt(const ASTContext& context) const;

    /// Forces resolution of both the type and the initializer using the given AST context
    /// instead of using the normal logic built into DeclaredType to determine the context.
    void forceResolveAt(const ASTContext& context) const;

private:
    void resolveType(const ASTContext& typeContext, const ASTContext& initializerContext) const;
    void checkType(const ASTContext& context) const;
    void mergePortTypes(
        const ASTContext& context, const ValueSymbol& sourceSymbol,
        const syntax::ImplicitTypeSyntax& implicit, SourceLocation location,
        std::span<const syntax::VariableDimensionSyntax* const> unpackedDimensions) const;

    template<bool IsInitializer,
             typename T = ASTContext> // templated to avoid having to include ASTContext.h
    T getASTContext() const;

    const Symbol& parent;

    mutable const Type* type = nullptr;
    union {
        const syntax::DataTypeSyntax* typeSyntax = nullptr;
        const DeclaredType* link;
    } typeOrLink;
    const syntax::SyntaxList<syntax::VariableDimensionSyntax>* dimensions = nullptr;

    mutable const Expression* initializer = nullptr;
    const syntax::ExpressionSyntax* initializerSyntax = nullptr;
    SourceLocation initializerLocation;

    bitmask<DeclaredTypeFlags> flags;
    uint32_t overrideIndex : 30;
    mutable uint32_t evaluating : 1;
    mutable uint32_t hasLink : 1;
};

} // namespace slang::ast
