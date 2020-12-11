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

enum class DeclaredTypeFlags {
    None = 0,
    InferImplicit = 1 << 0,
    RequireConstant = 1 << 1,
    LookupMax = 1 << 2,
    InProceduralContext = 1 << 3,
    AutomaticInitializer = 1 << 4,
    ForeachVar = 1 << 5,
    Port = 1 << 6,
    TypedefTarget = 1 << 7,
    NetType = 1 << 8,
    UserDefinedNetType = 1 << 9,
    FormalArgMergeVar = 1 << 10,
    Rand = 1 << 11,

    NeedsTypeCheck = Port | NetType | UserDefinedNetType | FormalArgMergeVar | Rand
};
BITMASK(DeclaredTypeFlags, Rand);

/// Ties together various syntax nodes that declare the type of some parent symbol
/// along with the logic necessary to resolve that type.
class DeclaredType {
public:
    explicit DeclaredType(const Symbol& parent,
                          bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);
    DeclaredType(const DeclaredType&) = delete;

    const Type& getType() const;

    void setType(const Type& newType) { type = &newType; }

    void setTypeSyntax(const DataTypeSyntax& newType) {
        typeSyntax = &newType;
        type = nullptr;
    }

    const DataTypeSyntax* getTypeSyntax() const { return typeSyntax; }

    void setDimensionSyntax(const SyntaxList<VariableDimensionSyntax>& newDimensions);
    const SyntaxList<VariableDimensionSyntax>* getDimensionSyntax() const { return dimensions; }

    const Expression* getInitializer() const;
    void setInitializer(const Expression& expr) { initializer = &expr; }

    void setInitializerSyntax(const ExpressionSyntax& syntax, SourceLocation loc) {
        initializerSyntax = &syntax;
        initializerLocation = loc;
        initializer = nullptr;
    }

    const ExpressionSyntax* getInitializerSyntax() const { return initializerSyntax; }
    SourceLocation getInitializerLocation() const { return initializerLocation; }

    void setFromDeclarator(const DeclaratorSyntax& decl);

    bool isEvaluating() const { return evaluating; }
    bool hasInitializer() const { return initializer != nullptr; }

    void addFlags(bitmask<DeclaredTypeFlags> toAdd) {
        type = nullptr;
        flags |= toAdd;
    }

    void mergeImplicitPort(const ImplicitTypeSyntax& implicit, SourceLocation location,
                           span<const VariableDimensionSyntax* const> unpackedDimensions);

    void copyTypeFrom(const DeclaredType& source);

    void resolveAt(const BindContext& context) const;

private:
    const Scope& getScope() const;
    void resolveType(const BindContext& initializerContext) const;
    const Type* resolveForeachVar(const BindContext& context) const;
    void checkType(const BindContext& context) const;
    void mergePortTypes(const BindContext& context, const ValueSymbol& sourceSymbol,
                        const ImplicitTypeSyntax& implicit, SourceLocation location,
                        span<const VariableDimensionSyntax* const> unpackedDimensions) const;

    template<typename T = BindContext> // templated to avoid having to include BindContext.h
    T getBindContext() const;

    const Symbol& parent;

    mutable const Type* type = nullptr;
    const DataTypeSyntax* typeSyntax = nullptr;
    const SyntaxList<VariableDimensionSyntax>* dimensions = nullptr;

    mutable const Expression* initializer = nullptr;
    const ExpressionSyntax* initializerSyntax = nullptr;
    SourceLocation initializerLocation;

    mutable bool evaluating = false;
    bitmask<DeclaredTypeFlags> flags;
};

} // namespace slang
