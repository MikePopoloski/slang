//------------------------------------------------------------------------------
//! @file DeclaredType.h
//! @brief Glue logic between symbols and their declared types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/syntax/SyntaxNode.h"

namespace slang {

class BindContext;
class ConstantValue;
class Expression;
class Scope;
class Symbol;
class Type;
class ValueSymbol;

struct DataTypeSyntax;
struct DeclaratorSyntax;
struct ExpressionSyntax;
struct ImplicitTypeSyntax;
struct VariableDimensionSyntax;

enum class SymbolIndex : uint32_t;

/// Various flags that control declared type resolution.
enum class DeclaredTypeFlags {
    /// No special flags specified.
    None = 0,

    /// If the declared type is implicit, the actual type should be
    /// inferred from the initializer. If this is not set, the type
    /// will be resolved as 'logic' if implicit syntax is provided.
    InferImplicit = 1 << 0,

    /// The bound initializer is required to be a constant expression.
    RequireConstant = 1 << 1,

    /// The initializer is for an automatic variable.
    AutomaticInitializer = 1 << 2,

    /// The type being bound is for a port.
    Port = 1 << 3,

    /// The type being bound is the target of a typedef.
    TypedefTarget = 1 << 4,

    /// The type being bound is a net type.
    NetType = 1 << 5,

    /// The type being bound is a user-defined net type.
    UserDefinedNetType = 1 << 6,

    /// The type being bound is part of port I/O declaration
    /// and should be merged with the formal argument declared
    /// elsewhere in the scope.
    FormalArgMergeVar = 1 << 7,

    /// The type being bound is for a random variable
    Rand = 1 << 8,

    /// The type being bound is a DPI return type.
    DPIReturnType = 1 << 9,

    /// The type being bound is for a DPI argument.
    DPIArg = 1 << 10,

    /// Specparams are allowed in the initializer expression, even if
    /// the expression is otherwise not constant.
    SpecparamsAllowed = 1 << 11,

    /// Allow use of the unbounded literal '$' in the initializer expression.
    AllowUnboundedLiteral = 1 << 12,

    /// The type must be one allowed in a sequence expression.
    RequireSequenceType = 1 << 13,

    /// A mask of flags that indicate additional type rules are needed to
    /// be checked after the type itself is resolved.
    NeedsTypeCheck = Port | NetType | UserDefinedNetType | FormalArgMergeVar | Rand |
                     DPIReturnType | DPIArg | RequireSequenceType
};
BITMASK(DeclaredTypeFlags, RequireSequenceType);

/// Ties together various syntax nodes that declare the type of some parent symbol
/// along with the logic necessary to resolve that type. Optionally includes an
/// initializer expression as well, which can be necessary when resolving types that
/// are implicitly inferred from the initializer.
class DeclaredType {
public:
    /// Constructs a new instance of the class.
    /// @param parent is the parent symbol that owns the declared type.
    /// @flags are optional additional flags that constraint type resolution.
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
    void setTypeSyntax(const DataTypeSyntax& newType) {
        typeSyntax = &newType;
        type = nullptr;
    }

    /// Gets the type syntax that was previously set via @a setTypeSyntax -- if any.
    /// Otherwise returns nullptr.
    const DataTypeSyntax* getTypeSyntax() const { return typeSyntax; }

    /// Sets an additional set of dimensions that represent the unpacked portion of
    /// the type declaration.
    void setDimensionSyntax(const SyntaxList<VariableDimensionSyntax>& newDimensions);

    /// Gets any previously set unpacked dimensions.
    const SyntaxList<VariableDimensionSyntax>* getDimensionSyntax() const { return dimensions; }

    /// Resolves and returns the initializer expression, if present. Otherwise returns nullptr.
    const Expression* getInitializer() const;

    /// Manually sets the resolved initializer expression, overriding anything
    /// that may have been resolved previously.
    void setInitializer(const Expression& expr) { initializer = &expr; }

    /// Sets the syntax for the initializer expression, which will be later used
    /// when resolution is requested. @param loc is the source location to use when
    /// reporting diagnostics about the initializer.
    void setInitializerSyntax(const ExpressionSyntax& syntax, SourceLocation loc) {
        initializerSyntax = &syntax;
        initializerLocation = loc;
        initializer = nullptr;
    }

    /// Gets the initializer syntax previously set by @a setInitializerSyntax
    const ExpressionSyntax* getInitializerSyntax() const { return initializerSyntax; }

    /// Gets the initializer location previously set by @a setInitializerSyntax
    SourceLocation getInitializerLocation() const { return initializerLocation; }

    /// Sets type and initializer information from the given declarator syntax.
    /// This is just convenient shorthand for invoking @a setTypeSyntax and
    /// @a setInitializerSyntax manually.
    void setFromDeclarator(const DeclaratorSyntax& decl);

    /// Returns true if this declared type is in the process of being resolved.
    /// This is used to detect cycles in the the type resolution process.
    bool isEvaluating() const { return evaluating; }

    /// Indicates whether this declared type has an already resolved initializer
    /// expression. If no initializer syntax has been set, or if it has but the
    /// initializer has not being resolved yet, returns false.
    bool hasResolvedInitializer() const { return initializer != nullptr; }

    /// Sets a separate, later position in the parent scope for binding the
    /// declared type and initializer. This is used for merged port symbols
    /// because their declared I/O location and symbol location may differ.
    void setOverrideIndex(SymbolIndex index) { overrideIndex = uint32_t(index); }

    /// Adds additional type resolution flags to constraint resolution behavior.
    /// This will clear any resolved type to force resolution again with the
    /// new flags set.
    void addFlags(bitmask<DeclaredTypeFlags> toAdd) {
        type = nullptr;
        initializer = nullptr;
        flags |= toAdd;
    }

    /// Perform a merge of implicit port information; this facilitates the non-ascii
    /// port system permitted by Verilog, where port I/O declarations are separate
    /// from the actual symbol declaration but may still carry some type info.
    void mergeImplicitPort(const ImplicitTypeSyntax& implicit, SourceLocation location,
                           span<const VariableDimensionSyntax* const> unpackedDimensions);

    /// Copies any type information from the provided @a source -- does not include
    /// initializer information.
    void copyTypeFrom(const DeclaredType& source);

    /// Resolves the initializer using the given bind context, which could
    /// differ from the binding context that is used for type resolution.
    void resolveAt(const BindContext& context) const;

    /// Forces resolution of both the type and the initializer using the given bind context
    /// instead of using the normal logic built into DeclaredType to determine the context.
    void forceResolveAt(const BindContext& context) const;

private:
    const Scope& getScope() const;
    void resolveType(const BindContext& typeContext, const BindContext& initializerContext) const;
    void checkType(const BindContext& context) const;
    void mergePortTypes(const BindContext& context, const ValueSymbol& sourceSymbol,
                        const ImplicitTypeSyntax& implicit, SourceLocation location,
                        span<const VariableDimensionSyntax* const> unpackedDimensions) const;

    template<bool IsInitializer,
             typename T = BindContext> // templated to avoid having to include BindContext.h
    T getBindContext() const;

    const Symbol& parent;

    mutable const Type* type = nullptr;
    const DataTypeSyntax* typeSyntax = nullptr;
    const SyntaxList<VariableDimensionSyntax>* dimensions = nullptr;

    mutable const Expression* initializer = nullptr;
    const ExpressionSyntax* initializerSyntax = nullptr;
    SourceLocation initializerLocation;

    bitmask<DeclaredTypeFlags> flags;
    uint32_t overrideIndex : 31;
    mutable uint32_t evaluating : 1;
};

} // namespace slang
