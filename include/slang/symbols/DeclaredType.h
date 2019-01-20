//------------------------------------------------------------------------------
// DeclaredType.h
// Glue logic between symbols and their declared types.
//
// File is under the MIT license; see LICENSE for details.
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
struct DataTypeSyntax;
struct ExpressionSyntax;
struct VariableDeclaratorSyntax;
struct VariableDimensionSyntax;

enum class DeclaredTypeFlags : uint8_t {
    None = 0,
    InferImplicit = 1,
    RequireConstant = 2,
    ForceSigned = 4
};
BITMASK_DEFINE_MAX_ELEMENT(DeclaredTypeFlags, ForceSigned);

/// Ties together various syntax nodes that declare the type of some parent symbol
/// along with the logic necessary to resolve that type.
class DeclaredType {
public:
    explicit DeclaredType(const Symbol& parent,
                          bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);
    DeclaredType(const DeclaredType&) = delete;

    const Type& getType() const {
        if (!type)
            resolveType();
        return *type;
    }

    void setType(const Type& newType) { type = &newType; }

    void setTypeSyntax(const DataTypeSyntax& newType) {
        typeSyntax = &newType;
        type = nullptr;
    }
    const DataTypeSyntax* getTypeSyntax() const { return typeSyntax; }

    void setDimensionSyntax(const SyntaxList<VariableDimensionSyntax>& newDimensions) {
        dimensions = &newDimensions;
        type = nullptr;
    }

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

    void setFromDeclarator(const VariableDeclaratorSyntax& decl);

    const ConstantValue& getConstantValue() const;

    bool isEvaluating() const { return evaluating; }
    bool isTypeResolved() const { return type != nullptr; }
    bitmask<DeclaredTypeFlags> getFlags() const { return flags; }

    void setForceSigned() {
        type = nullptr;
        flags |= DeclaredTypeFlags::ForceSigned;
    }

    void copyTypeFrom(const DeclaredType& source);

    static std::tuple<const Type*, const Expression*> resolveType(
        const DataTypeSyntax& typeSyntax, const SyntaxList<VariableDimensionSyntax>* dimensions,
        const ExpressionSyntax* initializerSyntax, const BindContext& context,
        bitmask<DeclaredTypeFlags> flags);

    static const Expression& resolveInitializer(const Type& type,
                                                const ExpressionSyntax& initializerSyntax,
                                                SourceLocation initializerLocation,
                                                const BindContext& context);

    static const Expression& resolveInitializer(
        const DataTypeSyntax& typeSyntax, const SyntaxList<VariableDimensionSyntax>* dimensions,
        const ExpressionSyntax& initializerSyntax, SourceLocation initializerLocation,
        const BindContext& context, bitmask<DeclaredTypeFlags> flags);

private:
    const Scope& getScope() const;
    void resolveType() const;

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